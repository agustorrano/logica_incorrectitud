module IncSepLogic

open FStar.Classical
open FStar.FunctionalExtensionality
open FStar.IndefiniteDescription

// ============================================================
// 1. Sintaxis y estados
// ============================================================

type var = string
type loc = nat
type value = 
  | Nat of nat 
  | Loc of loc

type cell =
  | Full of value
  | Empty
  | Unknown

type store = var ^-> value
type heap = loc ^-> cell

type expr =
  | Var : var -> expr
  | Const : nat -> expr
  | Plus : expr -> expr -> expr
  | Minus : expr -> expr -> expr
  | Times : expr -> expr -> expr
  | Eq : expr -> expr -> expr
  | Lt : expr -> expr -> expr
  | Gt : expr -> expr -> expr

type stmt =
  | Assign : var -> expr -> stmt
  | Nondet : var -> stmt
  | Skip : stmt
  | Error : stmt
  | Assume : expr -> stmt
  | Seq : stmt -> stmt -> stmt
  | Choice : stmt -> stmt -> stmt
  | Kleene : stmt -> stmt
  | Alloc : var -> stmt
  | Free : expr -> stmt
  | Load : var -> expr -> stmt
  | Store : expr -> expr -> stmt

type term_mode =
  | Ok
  | Er

type state = store & heap & term_mode
type cond = state -> prop

let rec eval_expr' (s : store) (e : expr) : GTot nat =
  match e with
  | Var x -> (
    match s x with
      | Nat n -> n
      | Loc l -> l
    )
  | Const n -> n
  | Plus e1 e2 -> eval_expr' s e1 + eval_expr' s e2
  | Minus e1 e2 -> 
    let res = eval_expr' s e1 - eval_expr' s e2 in
    if res >= 0 then res else 0
  | Times e1 e2 -> eval_expr' s e1 * eval_expr' s e2
  | Eq e1 e2 -> if eval_expr' s e1 = eval_expr' s e2
                then 1 else 0
  | Lt e1 e2 -> if eval_expr' s e1 < eval_expr' s e2
                then 1 else 0
  | Gt e1 e2 -> if eval_expr' s e1 > eval_expr' s e2
                then 1 else 0

let eval_expr (s : state) (e : expr) 
  : GTot nat = eval_expr' s._1 e

let eval_value (st : store) (e : expr) : GTot value =
  match e with
  | Var x -> st x
  | _ -> Nat (eval_expr' st e)

let override (#a : eqtype) (#b : Type) (f : a -> b) (x : a) (y : b) : (a ^-> b) =
  on a (fun z -> if z = x then y else f z)

unfold let state_equiv (s1 s2 : state) : prop =
  (forall x. s1._1 x == s2._1 x) /\
  (forall l. s1._2 l == s2._2 l) /\
  s1._3 == s2._3

let state_equiv_eq (s1 s2 : state)
  : Lemma (requires (state_equiv s1 s2))
          (ensures s1 == s2) =
  extensionality var (fun _ -> value) s1._1 s2._1;
  extensionality loc (fun _ -> cell) s1._2 s2._2

// ============================================================
// 2. Modelo y álgebra del heap
// ============================================================

let cell_disjoint (c1 c2 : cell) : prop =
  c1 == Unknown \/ c2 == Unknown

let cell_merge (c1 c2 : cell) : cell =
  match c1 with
  | Unknown -> c2
  | _ -> c1

let heap_merge (h1 h2 : heap) : heap =
  on loc (fun l -> cell_merge (h1 l) (h2 l))

let heaps_disjoint (h1 h2 : heap) : prop =
  forall l. cell_disjoint (h1 l) (h2 l)

let (><) (h1 h2 : heap) : prop =
  heaps_disjoint h1 h2

let heap_union (h1 h2 : heap { h1 >< h2 }) : heap =
  heap_merge h1 h2

let (<+>) = heap_union

let empty_heap : heap =
  on loc (fun _ -> Unknown)

let singleton_empty_heap (l : loc) : heap =
  on loc (fun l' -> if l' = l then Empty else Unknown)

let singleton_full_heap (l : loc) (v : value) : heap =
  on loc (fun l' -> if l' = l then Full v else Unknown)

let heap_without (h : heap) (l : loc) : heap =
  on loc (fun l' ->
    if l' = l then Unknown
    else h l')

// ============================================================
// 3. Semántica operacional
// ============================================================

type ok_state = s : state { s._3 == Ok }
type er_state = s : state { s._3 == Er }

noeq
type runsto : (p : stmt) -> (s0 : state) -> (s1 : state) -> Type0 =
  | R_Skip : s : ok_state -> runsto Skip s s
  
  | R_Error : s : ok_state -> runsto Error s (s._1, s._2, Er)
  
  | R_Assign : x : var -> e : expr -> s : ok_state -> 
    runsto (Assign x e) s (override s._1 x (eval_value s._1 e), s._2, Ok)
  
  | R_Nondet : s : ok_state -> #x : var -> v : value ->
    runsto (Nondet x) s (override s._1 x v, s._2, Ok)
  
  | R_Assume : s : ok_state -> #e : expr -> 
    squash (eval_expr s e =!= 0) ->
    runsto (Assume e) s s
  
  | R_SeqEr : #p : stmt -> #q : stmt -> #s : ok_state -> #t : er_state ->
    runsto p s t -> 
    runsto (Seq p q) s t
  
  | R_Seq : #p : stmt -> #q : stmt -> #s : ok_state -> #t : ok_state -> #u : state ->
    runsto p s t -> runsto q t u ->
    runsto (Seq p q) s u
  
  | R_ChoiceL : #p : stmt -> #q : stmt -> #s : ok_state -> #t : state ->
    runsto p s t -> runsto (Choice p q) s t
  
  | R_ChoiceR : #p : stmt -> #q : stmt -> #s: ok_state -> #t : state ->
    runsto q s t -> runsto (Choice p q) s t
  
  | R_Kleene0 : #p : stmt -> #s : ok_state -> 
    runsto (Kleene p) s s
  
  | R_KleeneS : #p : stmt -> #s : ok_state -> #t : state ->
    runsto (Seq (Kleene p) p) s t ->
    runsto (Kleene p) s t

  | R_Alloc : s : ok_state -> #x : var -> l : loc { l =!= 0 } -> v : value ->
    #(squash (s._2 l == Unknown \/ s._2 l == Empty)) ->
    runsto (Alloc x) s (override s._1 x (Loc l), override s._2 l (Full v), Ok)
  
  | R_Free : s : ok_state -> e : expr -> l : loc { l =!= 0 } -> v : value ->
    #(squash (eval_expr s e == l)) ->
    #(squash (s._2 l == Full v)) ->
    runsto (Free e) s (s._1, override s._2 l Empty, Ok)

  | R_FreeEr : s : ok_state -> e : expr ->
    #(squash (eval_expr s e =!= 0)) ->
    #(squash (s._2 (eval_expr s e) == Empty)) ->
    runsto (Free e) s (s._1, s._2, Er)
  
  | R_FreeNull : s : ok_state -> e : expr ->
    #(squash (eval_expr s e == 0)) ->
    runsto (Free e) s (s._1, s._2, Er)

  | R_Load : s : ok_state -> x : var -> e : expr -> v : value ->
    #(squash (eval_expr s e =!= 0)) ->
    #(squash (s._2 (eval_expr s e) == Full v)) ->
    runsto (Load x e) s (override s._1 x v, s._2, Ok)

  | R_LoadEr : s : ok_state -> x : var -> e : expr ->
    #(squash (eval_expr s e =!= 0)) ->
    #(squash (s._2 (eval_expr s e) == Empty)) ->
    runsto (Load x e) s (s._1, s._2, Er)

  | R_LoadNull : s : ok_state -> x : var -> e : expr ->
    #(squash (eval_expr s e == 0)) ->
    runsto (Load x e) s (s._1, s._2, Er)

  | R_Store : s : ok_state -> e1 : expr -> e2 : expr -> l : loc { l =!= 0 } -> v : value ->
    #(squash (s._2 l == Full v)) ->
    #(squash (eval_expr s e1 == l)) ->
    runsto (Store e1 e2) s (s._1, override s._2 l (Full (eval_value s._1 e2)), Ok)

  | R_StoreEr : s : ok_state -> e1 : expr -> e2 : expr ->
    #(squash (eval_expr s e1 =!= 0)) ->
    #(squash (s._2 (eval_expr s e1) == Empty)) ->
    runsto (Store e1 e2) s (s._1, s._2, Er)
  
  | R_StoreNull : s : ok_state -> e1 : expr -> e2 : expr ->
    #(squash (eval_expr s e1 == 0)) ->
    runsto (Store e1 e2) s (s._1, s._2, Er)

// ============================================================
// 4. Metateoría operacional
// ============================================================

let match_except_vars (vars : string -> prop) (st1 st2 : store) : prop =
  forall x. ~(vars x) ==> st1 x == st2 x

let rec modifies (p : stmt) (x : var) : prop =
  match p with
  | Assign y _ -> x = y
  | Nondet y -> x = y
  | Seq q r -> modifies q x \/ modifies r x
  | Choice q r -> modifies q x \/ modifies r x
  | Kleene q -> modifies q x
  | Alloc y -> x = y
  | Load y _ -> x = y
  | _ -> False

let rec lemma_runsto_modifies (#p : stmt) (#s0 #s1 : state) (r : runsto p s0 s1) 
  : Lemma (ensures match_except_vars (modifies p) s0._1 s1._1) (decreases r)=
  match r with
  | R_Seq r_p r_q ->
    lemma_runsto_modifies r_p;
    lemma_runsto_modifies r_q
  | R_SeqEr r_p ->
    lemma_runsto_modifies r_p
  | R_ChoiceL r_p ->
    lemma_runsto_modifies r_p
  | R_ChoiceR r_q ->
    lemma_runsto_modifies r_q
  | R_KleeneS r_seq ->
    lemma_runsto_modifies r_seq
  | _ -> ()

let rec lemma_runsto_disjoint (#p : stmt) (#s0 : state) (#s1 : state) 
  (h_fr : heap) (r : runsto p s0 s1) :
  Lemma (requires s1._2 >< h_fr)
        (ensures s0._2 >< h_fr) (decreases r) = 
  match r with
  | R_SeqEr r_p ->
    lemma_runsto_disjoint h_fr r_p
  | R_Seq r_p r_q ->
    lemma_runsto_disjoint h_fr r_q;
    lemma_runsto_disjoint h_fr r_p
  | R_ChoiceL r_p ->
    lemma_runsto_disjoint h_fr r_p
  | R_ChoiceR r_q ->
    lemma_runsto_disjoint h_fr r_q
  | R_KleeneS r_seq ->
    lemma_runsto_disjoint h_fr r_seq
  | _ -> ()

let rec r_frame (#p : stmt) (#s0 : state) (#s1 : state)
  (r : runsto p s0 s1) (h_fr : heap)
  (#_ : squash (s0._2 >< h_fr))
  (#_ : squash (s1._2 >< h_fr)) :
  GTot (runsto p 
    (s0._1, s0._2 <+> h_fr, s0._3) (s1._1, s1._2 <+> h_fr, s1._3))
  (decreases r) =
  let s0_fr = (s0._1, s0._2 <+> h_fr, s0._3) in
  let s1_fr = (s1._1, s1._2 <+> h_fr, s1._3) in
  match r with
  | R_Skip _ ->
    R_Skip s0_fr
  | R_Error _ ->
    R_Error s0_fr
  | R_Assign x e s ->
    R_Assign x e s0_fr
  | R_Nondet _ #x v ->
    R_Nondet s0_fr #x v
  | R_Assume _ #e _ ->
    R_Assume s0_fr #e ()
  | R_SeqEr #p #q r_p ->
    let r_p_fr = r_frame r_p h_fr #() #() in
    let r_seq_er = R_SeqEr #p #q #s0_fr #s1_fr r_p_fr in
    r_seq_er
  | R_Seq #p #q #s #t r_p r_q ->
    lemma_runsto_disjoint h_fr r_q;
    let r_p_fr = r_frame r_p h_fr #() #() in
    let r_q_fr = r_frame r_q h_fr #() #() in
    let (st_t, hp_t, m_t) = t in
    let s_mid_fr = (st_t, hp_t <+> h_fr, m_t) in
    let r_seq = R_Seq #p #q #s0_fr #s_mid_fr #s1_fr r_p_fr r_q_fr in
    r_seq
  | R_ChoiceL #p #q r_p ->
    let r_p_fr = r_frame r_p h_fr #() #() in
    let r_choice_l = R_ChoiceL #p #q #s0_fr #s1_fr r_p_fr in
    r_choice_l
  | R_ChoiceR #p #q r_q ->
    let r_q_fr = r_frame r_q h_fr #() #() in
    let r_choice_r = R_ChoiceR #p #q #s0_fr #s1_fr r_q_fr in
    r_choice_r
  | R_Kleene0 #p ->
    R_Kleene0 #p #s0_fr
  | R_KleeneS #p r_seq ->
    let r_seq_fr = r_frame r_seq h_fr #() #() in
    let r_kleene = R_KleeneS #p #s0_fr #s1_fr r_seq_fr in
    r_kleene
  | R_Alloc _ #x l v ->
    state_equiv_eq
      (override s0_fr._1 x (Loc l), override s0_fr._2 l (Full v), s0_fr._3)
      s1_fr;
    R_Alloc s0_fr #x l v
  | R_Free s e l v ->
    state_equiv_eq
      (s0_fr._1, override s0_fr._2 l Empty, s0_fr._3) s1_fr;
    R_Free s0_fr e l v
  | R_FreeEr s e ->
    R_FreeEr s0_fr e
  | R_FreeNull s e ->
    R_FreeNull s0_fr e
  | R_Load s x e v ->
    R_Load s0_fr x e v
  | R_LoadEr s x e ->
    R_LoadEr s0_fr x e
  | R_LoadNull s x e ->
    R_LoadNull s0_fr x e
  | R_Store s e1 e2 l v ->
    state_equiv_eq
      (s0_fr._1, override s0_fr._2 l (Full (eval_value s0_fr._1 e2)), s0_fr._3)
      s1_fr;
    R_Store s0_fr e1 e2 l v
  | R_StoreEr s e1 e2 ->
    R_StoreEr s0_fr e1 e2
  | R_StoreNull s e1 e2 ->
    R_StoreNull s0_fr e1 e2

// ============================================================
// 5. Lógica de Incorrectitud de Separación
// ============================================================

let rec fv_expr (e : expr) (x : var) : prop =
  match e with
  | Var y -> x = y
  | Const _ -> False
  | Plus e1 e2 | Minus e1 e2 | Times e1 e2
  | Eq e1 e2 | Lt e1 e2 | Gt e1 e2 ->
    fv_expr e1 x \/ fv_expr e2 x

let rec fv_stmt (p : stmt) (x: var) : prop =
  match p with
  | Assign y e -> x = y \/ fv_expr e x
  | Nondet y -> x = y
  | Assume e -> fv_expr e x
  | Seq p1 p2 -> fv_stmt p1 x \/ fv_stmt p2 x
  | Choice p1 p2 -> fv_stmt p1 x \/ fv_stmt p2 x
  | Kleene p1 -> fv_stmt p1 x
  | Alloc y -> x = y
  | Free e -> fv_expr e x
  | Load y e -> x = y \/ fv_expr e x
  | Store e1 e2 -> fv_expr e1 x \/ fv_expr e2 x
  | _ -> False

let exists_var (x : var) (c : cond) : cond =
  fun s -> exists v.
    c (override s._1 x v, s._2, s._3)

let points_to_empty (l : loc) : cond =
  fun (st, hp, m) -> 
    l =!= 0 /\
    hp l == Empty /\
    forall l'. (l' <> l) ==> (hp l' == Unknown)
  
let points_to (l : loc) (v : value) : cond =
  fun (st, hp, m) -> 
  l =!=0 /\
  hp l == Full v /\
  forall l'. (l' <> l) ==> (hp l' == Unknown)

let emp : cond =
  fun (st, hp, m) -> forall l. hp l == Unknown

unfold
let sep_conj (p q : cond) : cond =
  fun (st, hp, m) -> 
    exists h1 h2.
      h1 >< h2 /\
      hp == (h1 <+> h2) /\
      p (st, h1, m) /\ q (st, h2, m)

unfold let ( ** ) = sep_conj

let introduce_frame (p fr : cond) (s : state) (h_local h_frame : heap)
  : Lemma (requires h_local >< h_frame /\
            (forall l. s._2 l == (h_local <+> h_frame) l) /\
            p (s._1, h_local, s._3) /\ fr (s._1, h_frame, s._3))
          (ensures (p ** fr) s) =
  extensionality loc (fun _ -> cell) s._2 (h_local <+> h_frame);
  exists_intro (fun h -> h_local >< h /\ s._2 == (h_local <+> h) /\
    p (s._1, h_local, s._3) /\ fr (s._1, h, s._3)) h_frame;
  exists_intro (fun h -> exists f. h >< f /\ s._2 == (h <+> f) /\
    p (s._1, h, s._3) /\ fr (s._1, f, s._3)) h_local

let points_to_flex (l : loc) (v : value) : cond =
  points_to l v ** (fun _ -> True)

let independent_on_vars (vars : string -> prop) (c : cond) : prop =
  forall (st1 st2 : store) (hp : heap) (m1 m2 : term_mode).
    match_except_vars vars st1 st2 ==> (c (st1, hp, m1) <==> c (st2, hp, m2))

unfold let is_ok (c : cond) : cond = fun s -> c s /\ s._3 == Ok

unfold
let kleene_pre (variant : nat -> cond) : cond =
  is_ok (variant 0)

unfold
let kleene_post (variant : nat -> cond) : cond =
  is_ok (fun s -> exists (n : nat). variant n s)

noeq
[@@erasable]
type isl_triple : (pre : cond) -> (p : stmt) -> (post : cond) -> Type =
  | ISL_Assign : #pre : cond -> x : var -> e : expr ->
    isl_triple (is_ok pre) (Assign x e) 
      (is_ok (fun s -> exists (st_init : store). 
        pre (st_init, s._2, s._3) /\ (s._1 x == eval_value st_init e /\
        (forall y. (y <> x) ==> s._1 y == st_init y))))
  
  | ISL_Nondet : #pre : cond -> x : var -> 
    isl_triple (is_ok pre) (Nondet x)
      (is_ok (fun s -> exists v.
        pre (override s._1 x v, s._2, s._3)))
  
  | ISL_Skip : #pre : cond ->
    isl_triple (is_ok pre) Skip (is_ok pre)
  
  | ISL_Error : #pre : cond ->
    isl_triple (is_ok pre) Error
      (fun s -> let (st, hp, m) = s in m == Er /\ pre (st, hp, Ok))
  
  | ISL_Assume : #pre : cond -> e : expr ->
    isl_triple (is_ok pre) (Assume e)
      (is_ok (fun s -> pre s /\ (eval_expr s e =!= 0)))
  
  | ISL_Seq : #p : stmt -> #q : stmt ->
    #pre : cond -> #mid : cond -> #post : cond ->
    isl_triple (is_ok pre) p mid ->
    isl_triple (is_ok mid) q post ->
    isl_triple (is_ok pre) (Seq p q) 
      (fun s -> post s \/ (s._3 == Er /\ mid s))
  
  | ISL_ChoiceL : #p : stmt -> #q : stmt ->
    #pre : cond -> #post : cond ->
    isl_triple (is_ok pre) p post ->
    isl_triple (is_ok pre) (Choice p q) post
  
  | ISL_ChoiceR : #p : stmt -> #q : stmt ->
    #pre : cond -> #post : cond ->
    isl_triple (is_ok pre) q post ->
    isl_triple (is_ok pre) (Choice p q) post
  
  | ISL_Kleene0 : #p : stmt -> #pre : cond ->
    isl_triple (is_ok pre) (Kleene p) (is_ok pre)
  
  | ISL_KleeneS : #p : stmt -> #pre : cond -> #post : cond ->
    isl_triple (is_ok pre) (Seq (Kleene p) p) post ->
    isl_triple (is_ok pre) (Kleene p) post
  
  | ISL_KleeneVariant : #variant : (nat -> cond) -> #p : stmt ->
    step_proof : (n : nat ->
      isl_triple (is_ok (variant n)) p (is_ok (variant (n + 1)))) ->
    isl_triple (kleene_pre variant) (Kleene p) (kleene_post variant)
  
  | ISL_Exists : #p : stmt -> #pre : cond -> #post : cond -> x : var ->
    isl_triple (is_ok pre) p post ->
    squash(~(fv_stmt p x)) ->
    isl_triple (is_ok (exists_var x pre)) p (exists_var x post)

  | ISL_Consequence : #pre : cond -> #p : stmt ->
    #post : cond -> pre' : cond -> post' : cond ->
    isl_triple (is_ok pre) p post ->
    squash (forall x. pre x ==> pre' x) ->
    squash (forall x. post' x ==> post x) ->
    isl_triple (is_ok pre') p post'

  | ISL_Disjunction : #pre1 : cond -> #pre2 : cond ->
    #p : stmt -> #post1 : cond -> #post2 : cond ->
    isl_triple (is_ok pre1) p post1 ->
    isl_triple (is_ok pre2) p post2 ->
    isl_triple (is_ok (fun s -> pre1 s \/ pre2 s)) p
      (fun s -> post1 s \/ post2 s)

  | ISL_Frame : #pre : cond -> #p : stmt ->
    #post : cond -> fr : cond ->
    isl_triple (is_ok pre) p post ->
    squash (independent_on_vars (modifies p) fr) ->
    isl_triple (is_ok (pre ** fr)) p
      (post ** fr)
  
  | ISL_Alloc1 : #pre : cond -> x : var ->
    isl_triple (is_ok pre) (Alloc x)
      (is_ok (fun s -> exists l v.
        s._1 x == Loc l /\
        l =!= 0 /\
        points_to l v s /\
        (exists x_old. pre (override s._1 x x_old, override s._2 l Unknown, Ok))))

  | ISL_Alloc2 : #pre : cond -> x : var ->
    isl_triple (is_ok pre) (Alloc x)
      (is_ok (fun s -> exists (l : loc) (v x_old : value).
        s._1 x == Loc l /\
        l =!= 0 /\
        points_to l v s /\
        pre (override s._1 x x_old, override s._2 l Empty, Ok)))
  
  | ISL_Free : #pre : cond -> e : expr ->
    isl_triple (is_ok pre) (Free e)
      (is_ok (fun s -> exists (v : value).
        points_to_empty (eval_expr s e) s /\
        pre (s._1, override s._2 (eval_expr s e) (Full v), Ok)))

  | ISL_FreeEr : #pre : cond -> e : expr ->
    isl_triple (is_ok pre) (Free e)
      (fun s ->
        s._3 == Er /\
        points_to_empty (eval_expr s e) s /\
        pre (s._1, s._2, Ok))

  | ISL_FreeNull : #pre : cond -> e : expr ->
    isl_triple (is_ok pre) (Free e)
      (fun s -> s._3 == Er /\ eval_expr s e == 0 /\ pre (s._1, s._2, Ok))
  
  | ISL_Load : #pre : cond -> x : var -> e : expr ->
    isl_triple (is_ok pre) (Load x e)
      (is_ok (fun s -> exists l v x_old.
        eval_expr (override s._1 x x_old, s._2, Ok) e == l /\
        points_to l v s /\
        s._1 x == v /\
        pre (override s._1 x x_old, s._2, Ok)))

  | ISL_LoadEr : #pre : cond -> x : var -> e : expr ->
    isl_triple (is_ok pre) (Load x e)
      (fun s ->
        s._3 == Er /\
        points_to_empty (eval_expr s e) s /\
        pre (s._1, s._2, Ok))

  | ISL_LoadNull : #pre : cond -> x : var -> e : expr ->
    isl_triple (is_ok pre) (Load x e)
      (fun s -> s._3 == Er /\ eval_expr s e == 0 /\ pre (s._1, s._2, Ok))
  
  | ISL_Store : #pre : cond -> e1 : expr -> e2 : expr ->
    isl_triple (is_ok pre) (Store e1 e2)
      (is_ok (fun s ->
        points_to (eval_expr s e1) (eval_value s._1 e2) s /\
        (exists v_old. pre (s._1, override s._2 (eval_expr s e1) (Full v_old), Ok))))

  | ISL_StoreEr : #pre : cond -> e1 : expr -> e2 : expr ->
    isl_triple (is_ok pre) (Store e1 e2)
      (fun s -> 
        s._3 == Er /\ 
        points_to_empty (eval_expr s e1) s /\
        pre (s._1, s._2, Ok))

  | ISL_StoreNull : #pre : cond -> e1 : expr -> e2 : expr ->
    isl_triple (is_ok pre) (Store e1 e2)
      (fun s -> 
        s._3 == Er /\ 
        eval_expr s e1 == 0 /\
        pre (s._1, s._2, Ok))

// ============================================================
// 6. Soundness de la ISL
// ============================================================

let set_var (s : state) (x : var) (v : value) : state =
  (override s._1 x v, s._2, s._3)

let rec eval_expr_fresh (s : state) (e : expr) (x : var) (v : value)
  : Lemma (requires (~(fv_expr e x)))
          (ensures (eval_expr (set_var s x v) e == eval_expr s e)) (decreases e) =
  match e with
  | Var _ | Const _ -> ()
  | Plus e1 e2 | Minus e1 e2 | Times e1 e2
  | Eq e1 e2 | Lt e1 e2 | Gt e1 e2 ->
    eval_expr_fresh s e1 x v;
    eval_expr_fresh s e2 x v

let eval_value_fresh (s : state) (e : expr) (x : var) (v : value)
  : Lemma (requires ~(fv_expr e x))
          (ensures eval_value (set_var s x v)._1 e == eval_value s._1 e) =
  match e with
  | Var _ -> ()
  | _ -> eval_expr_fresh s e x v

let rec r_fresh (#p : stmt) (#s0 #s1 : state)
  (r : runsto p s0 s1) (x : var) (v : value)
  (#_ : squash (~(fv_stmt p x)))
  : GTot (runsto p (set_var s0 x v) (set_var s1 x v))
  (decreases r) =
  let s0_f = set_var s0 x v in
  let s1_f = set_var s1 x v in
  match r with
  | R_Skip _ -> R_Skip s0_f
  | R_Error _ -> R_Error s0_f
  | R_Assign y e s ->
    eval_value_fresh s e x v;
    state_equiv_eq (override s0_f._1 y (eval_value s0_f._1 e), s0_f._2, s0_f._3) s1_f;
    R_Assign y e s0_f
  | R_Nondet _ #y w ->
    state_equiv_eq (override s0_f._1 y w, s0_f._2, s0_f._3) s1_f;
    R_Nondet s0_f #y w
  | R_Assume s #e _ ->
    eval_expr_fresh s e x v;
    R_Assume s0_f #e ()
  | R_SeqEr #p #q r_p ->
    R_SeqEr #p #q #s0_f #s1_f (r_fresh r_p x v #())
  | R_Seq #p #q #s #t r_p r_q ->
    let r_p_f = r_fresh r_p x v #() in
    let r_q_f = r_fresh r_q x v #() in
    R_Seq #p #q #s0_f #(set_var t x v) #s1_f r_p_f r_q_f
  | R_ChoiceL #p #q r_p ->
    R_ChoiceL #p #q #s0_f #s1_f (r_fresh r_p x v #())
  | R_ChoiceR #p #q r_q ->
    R_ChoiceR #p #q #s0_f #s1_f (r_fresh r_q x v #())
  | R_Kleene0 #p ->
    R_Kleene0 #p #s0_f
  | R_KleeneS #p r_seq ->
    R_KleeneS #p #s0_f #s1_f (r_fresh r_seq x v #())
  | R_Alloc _ #y l w ->
    state_equiv_eq
      (override s0_f._1 y (Loc l),
      override s0_f._2 l (Full w), s0_f._3)
      s1_f;
    R_Alloc s0_f #y l w
  | R_Free s e l w ->
    eval_expr_fresh s e x v;
    R_Free s0_f e l w
  | R_FreeEr s e ->
    eval_expr_fresh s e x v;
    R_FreeEr s0_f e
  | R_FreeNull s e ->
    eval_expr_fresh s e x v;
    R_FreeNull s0_f e
  | R_Load s y e w ->
    eval_expr_fresh s e x v;
    state_equiv_eq (override s0_f._1 y w, s0_f._2, s0_f._3) s1_f;
    R_Load s0_f y e w
  | R_LoadEr s y e ->
    eval_expr_fresh s e x v;
    R_LoadEr s0_f y e
  | R_LoadNull s y e ->
    eval_expr_fresh s e x v;
    R_LoadNull s0_f y e
  | R_Store s e1 e2 l w ->
    eval_expr_fresh s e1 x v;
    eval_value_fresh s e2 x v;
    R_Store s0_f e1 e2 l w
  | R_StoreEr s e1 e2 ->
    eval_expr_fresh s e1 x v;
    R_StoreEr s0_f e1 e2
  | R_StoreNull s e1 e2 ->
    eval_expr_fresh s e1 x v;
    R_StoreNull s0_f e1 e2

let rec soundness
  (p : stmt) (pre : cond) (post : cond)
  (pf : isl_triple pre p post)
  (s1 : state { post s1 })
  : GTot (s0 : state { pre s0 } & runsto p s0 s1) (decreases pf) 
  = match pf with
  | ISL_Assign #pre #x #e ->
    let (st1, hp1, m) = s1 in
    let st_init = indefinite_description_ghost store (fun st_i -> pre (st_i, hp1, m) 
      /\ st1 x == eval_value st_i e
      /\ (forall y. y <> x ==> st1 y == st_i y))
    in
    let s0 = (st_init, hp1, Ok) in
    let pf0 = R_Assign x e s0 in
    state_equiv_eq (override st_init x (eval_value s0._1 e), hp1, Ok) s1;
    (|s0, pf0|)
  
  | ISL_Nondet #pre #x -> 
    let (st1, hp1, m) = s1 in
    let v = indefinite_description_ghost _ (fun v -> pre (override st1 x v, hp1, m)) in
    let s0 = (override st1 x v, hp1, Ok) in
    let pf0 = R_Nondet s0 #x (st1 x) in
    state_equiv_eq (override s0._1 x (st1 x), hp1, Ok) s1;
    (|s0, pf0|)

  | ISL_Frame #p_pre #p_cmd #p_post fr pf_p _ ->
    let unfold p_two (h_local h_fr : heap) : prop = 
      h_local >< h_fr /\ 
      s1._2 == (h_local <+> h_fr) /\ 
      p_post (s1._1, h_local, s1._3) /\ 
      fr (s1._1, h_fr, s1._3)
    in
    let h_local = indefinite_description_ghost heap (fun h_local ->
      exists h_fr. p_two h_local h_fr) in
    let h_fr = indefinite_description_ghost heap (fun h_fr ->
      p_two h_local h_fr) in
    let (|s0_local, r_local|) = 
      soundness p_cmd (is_ok p_pre) p_post pf_p (s1._1, h_local, s1._3) in
    let (st0, hp0, m0) = s0_local in
    lemma_runsto_disjoint h_fr r_local;
    let s0 : state = (st0, hp0 <+> h_fr, m0) in
    let r_global = r_frame r_local h_fr #() #() in
    lemma_runsto_modifies r_local;
    (|s0, r_global|)

  | ISL_Skip ->
    let s0 = s1 in
    let r = R_Skip s0 in
    (|s0, r|)
  
  | ISL_Error ->
    let (st, hp, m1) = s1 in
    let s0 = (st, hp, Ok) in
    let r = R_Error s0 in
    (|s0, r|)

  | ISL_Assume #pre #e ->
    let s0 = s1 in
    let r = R_Assume s0 #e () in
    (|s0, r|)

  | ISL_Seq #p #q #pre #mid #post pf_p pf_q ->
    if t2b (post s1) then
      let (|s_mid, r_q|) = 
        soundness q (is_ok mid) post pf_q s1 in
      let (|s0, r_p|) =
        soundness p (is_ok pre) mid pf_p s_mid in
      let r = R_Seq #p #q #s0 #s_mid #s1 r_p r_q in
      (|s0, r|)
    else
      let (|s0, r_p|) =
        soundness p (is_ok pre) mid pf_p s1 in
      let r = R_SeqEr #p #q #s0 #s1 r_p in
      (|s0, r|)

  | ISL_ChoiceL #p #q #pre #post pf_p ->
    let (|s0, r_p|) =
      soundness p (is_ok pre) post pf_p s1 in
    let r = R_ChoiceL #p #q #s0 #s1 r_p in
    (|s0, r|)

  | ISL_ChoiceR #p #q #pre #post pf_q -> 
    let (|s0, r_q|) =
      soundness q (is_ok pre) post pf_q s1 in
    let r = R_ChoiceR #p #q #s0 #s1 r_q in
    (|s0, r|)

  | ISL_Kleene0 #p ->
    let s0 = s1 in
    let r = R_Kleene0 #p #s0 in
    (|s0, r|)

  | ISL_KleeneS #p #pre #post pf_seq ->
    let (|s0, r_seq|) =
      soundness (Seq (Kleene p) p) (is_ok pre) post pf_seq s1 in
    let r = R_KleeneS #p #s0 #s1 r_seq in
    (|s0, r|)
  
  | ISL_KleeneVariant #variant #p pf_var ->
    let p_n (n : nat) : prop = variant n s1 /\ s1._3 == Ok in
    let n = indefinite_description_ghost _ p_n in
    let rec aux (m : nat) (t : state { variant m t /\ t._3 == Ok})
      : GTot (s0 : state { variant 0 s0 /\ s0._3 == Ok } & runsto (Kleene p) s0 t) (decreases m) =
      if m = 0 then
        let s0 = t in
        let r = R_Kleene0 in
        (|s0, r|)
      else
        let m' = m - 1 in
        let pf_p = pf_var m' in
        let (|s_mid, r_p|) = 
          soundness p (is_ok (variant m')) (is_ok (variant (m' + 1))) pf_p t in
        let (|s0, r_kleene|) = aux m' s_mid in
        let r_seq = 
          R_Seq #(Kleene p) #p #s0 #s_mid #t r_kleene r_p in
        let r = R_KleeneS #p #s0 #t r_seq in
        (|s0, r|)
    in
    aux n s1
  
  | ISL_Exists #p #pre #post x pf_p _ ->
    let v = indefinite_description_ghost value (fun v -> post (set_var s1 x v)) in
    let s1_v = set_var s1 x v in
    let (|s0_v, r|) = soundness p (is_ok pre) post pf_p s1_v in
    let orig = s1._1 x in
    let s0 = set_var s0_v x orig in
    let r' = r_fresh r x orig #() in
    state_equiv_eq (set_var s1_v x orig) s1;
    state_equiv_eq (set_var s0 x (s0_v._1 x)) s0_v;
    exists_intro (fun w -> pre (set_var s0 x w)) (s0_v._1 x);
    (|s0, r'|)
  
  | ISL_Consequence #pre #p #post pre' post' pf_p _ _ ->
    let (|s0, r|) = soundness p (is_ok pre) post pf_p s1 in
    (|s0, r|)

  | ISL_Disjunction #pre1 #pre2 #p #post1 #post2 pf_p1 pf_p2 ->
    if t2b (post1 s1) then
      let (|s0, r|) = soundness p (is_ok pre1) post1 pf_p1 s1 in
      (|s0, r|)
    else
      let (|s0, r|) = soundness p (is_ok pre2) post2 pf_p2 s1 in
      (|s0, r|)

  | ISL_Alloc1 #pre #x -> 
    let (st1, hp1, m1) = s1 in
    let unfold p_lv (l_i : loc) (v_i : value) : prop =
      st1 x == Loc l_i /\ l_i =!= 0 /\ points_to l_i v_i s1
    in
    let l = indefinite_description_ghost loc (fun l ->
      exists v. p_lv l v) in
    let v = indefinite_description_ghost value (fun v ->
      p_lv l v) in
    let p_xold (x_o : value) : prop =
      pre (override st1 x x_o, override hp1 l Unknown, Ok)
    in
    let x_old = indefinite_description_ghost value p_xold in
    let st0 = override st1 x x_old in
    let hp0 = override hp1 l Unknown in
    let s0 : state = (st0, hp0, Ok) in
    let r = R_Alloc s0 #x l v #() in
    state_equiv_eq (override st0 x (Loc l), override hp0 l (Full v), Ok) s1;
    (|s0, r|)

  | ISL_Alloc2 #pre #x ->
    let (st1, hp1, m1) = s1 in
    let unfold p_lv (l_i : loc) (v_i : value) : prop =
      st1 x == Loc l_i /\ l_i =!= 0 /\ points_to l_i v_i s1
    in
    let l = indefinite_description_ghost loc (fun l ->
      exists v. p_lv l v) in
    let v = indefinite_description_ghost value (fun v ->
      p_lv l v) in
    let p_xold (x_o : value) : prop =
      pre (override st1 x x_o, override hp1 l Empty, Ok)
    in
    let x_old = indefinite_description_ghost value p_xold in
    let st0 = override st1 x x_old in
    let hp0 = override hp1 l Empty in
    let s0 : state = (st0, hp0, Ok) in
    let r = R_Alloc s0 #x l v in
    state_equiv_eq (override st0 x (Loc l), override hp0 l (Full v), Ok) s1;
    (|s0, r|)

  | ISL_Free #pre e -> 
    let (st1, hp1, m1) = s1 in
    let l = eval_expr s1 e in
    let p_v (v_i : value) : prop = 
      m1 == Ok /\ points_to_empty l s1 /\ pre (st1, override hp1 l (Full v_i), Ok) 
    in
    let v = indefinite_description_ghost value p_v in
    let st0 = st1 in
    let hp0 = override hp1 l (Full v) in
    let s0 = (st0, hp0, Ok) in
    let r = R_Free s0 e l v in
    state_equiv_eq (st0, override hp0 l Empty, Ok) s1;
    (|s0, r|)

  | ISL_FreeEr #pre e ->
    let (st, hp, _) = s1 in
    let s0 = (st, hp, Ok) in
    let r = R_FreeEr s0 e in
    (|s0, r|)

  | ISL_FreeNull #pre e ->
    let (st, hp, _) = s1 in
    let s0 = (st, hp, Ok) in
    let r = R_FreeNull s0 e in
    (|s0, r|)

  | ISL_Load #pre #x #e ->
    let (st1, hp1, m1) = s1 in
    let p_xold (x_o : value) : prop =
      exists (l_i : loc) (v_i : value).
        eval_expr (override st1 x x_o, hp1, Ok) e == l_i /\
        points_to l_i v_i s1 /\ st1 x = v_i /\
        pre (override st1 x x_o, hp1, Ok)
    in
    let x_old = indefinite_description_ghost value p_xold in
    let unfold p_lv (l_i : loc) (v_i : value) : prop =
      eval_expr (override st1 x x_old, hp1, Ok) e == l_i /\ 
      points_to l_i v_i s1 /\ st1 x == v_i /\
      pre (override st1 x x_old, hp1, Ok)
    in
    let l = indefinite_description_ghost loc (fun l ->
      exists v. p_lv l v) in
    let v = indefinite_description_ghost value (fun v ->
      p_lv l v) in
    let st0 = override st1 x x_old in
    let hp0 = hp1 in
    let s0 : state = (st0, hp0, Ok) in
    exists_intro (fun v_i -> points_to l v_i s0) v;
    let r = R_Load s0 x e v in
    let st1' = override st0 x v in
    state_equiv_eq (st1', hp0, Ok) s1;
    (|s0, r|)

  | ISL_LoadEr #pre #x #e ->
    let (st, hp, m1) = s1 in
    let s0 = (st, hp, Ok) in
    let l = eval_expr s0 e in
    let r = R_LoadEr s0 x e in
    (|s0, r|)

  | ISL_LoadNull #pre #x #e ->
    let (st, hp, m1) = s1 in
    let s0 = (st, hp, Ok) in
    let r = R_LoadNull s0 x e in
    (|s0, r|)

  | ISL_Store #pre #e1 #e2 -> 
    let (st1, hp1, m1) = s1 in
    let p_l (l_i : loc) : prop =
      eval_expr s1 e1 == l_i /\ points_to l_i (eval_value s1._1 e2) s1
    in
    let l = indefinite_description_ghost loc p_l in
    let p_vold (v_o : value) : prop =
      pre (st1, override hp1 l (Full v_o), Ok)
    in
    let v_old = indefinite_description_ghost value p_vold in
    let st0 = st1 in
    let hp0 = override hp1 l (Full v_old) in
    let s0 = (st0, hp0, Ok) in
    exists_intro (fun v_i -> eval_expr s0 e1 == l /\ points_to l v_i s0) v_old;
    exists_intro (fun l_i -> exists v_i. eval_expr s0 e1 == l_i /\ points_to l_i v_i s0) l;
    let r = R_Store s0 e1 e2 l v_old in
    let hp1' = override hp0 l (Full (eval_value s0._1 e2)) in
    state_equiv_eq (st0, hp1', Ok) s1;
    (|s0, r|)

  | ISL_StoreEr #pre e1 e2 ->
    let (st, hp, m1) = s1 in
    let s0 = (st, hp, Ok) in
    let l = eval_expr s0 e1 in
    let r = R_StoreEr s0 e1 e2 in
    (|s0, r|)

  | ISL_StoreNull #pre #e1 #e2 ->
    let (st, hp, m1) = s1 in
    let s0 = (st, hp, Ok) in
    let r = R_StoreNull s0 e1 e2 in
    (|s0, r|)

// ============================================================
// 7. Footprints
// ============================================================

noeq
type footprint : stmt -> state -> state -> Type0 =
  | F_Skip : st : store ->
    footprint Skip (st, empty_heap, Ok) (st, empty_heap, Ok)
  
  | F_Assign : st : store -> x : var -> e : expr ->
    footprint (Assign x e) (st, empty_heap, Ok) 
    (override st x (eval_value st e), empty_heap, Ok)
  
  | F_Nondet : st : store -> x : var -> v : value ->
    footprint (Nondet x) (st, empty_heap, Ok)
    (override st x v, empty_heap, Ok)
  
  | F_Assume : st : store -> e : expr ->
    #(squash (eval_expr (st, empty_heap, Ok) e =!= 0)) ->
    footprint (Assume e) (st, empty_heap, Ok) (st, empty_heap, Ok)
  
  | F_Error : st : store ->
    footprint Error (st, empty_heap, Ok) (st, empty_heap, Er)
  
  | F_Seq : p : stmt -> q : stmt -> st0 : store -> stm : store ->
    st1 : store -> h_common : heap -> 
    h_p : heap { h_common >< h_p } -> 
    h_q : heap { h_common >< h_q /\ h_p >< h_q } -> 
    h0 : heap { h0 >< h_q } -> h1 : heap { h1 >< h_p } -> 
    m1 : term_mode ->
    footprint p (st0, h0, Ok) (stm, h_common <+> h_p, Ok) ->
    footprint q (stm, h_common <+> h_q, Ok) (st1, h1, m1) ->
    footprint (Seq p q) (st0, h0 <+> h_q, Ok) (st1, h1 <+> h_p, m1)
  
  | F_SeqEr : p : stmt -> q : stmt -> 
    s : ok_state -> t : er_state ->
    footprint p s t ->
    footprint (Seq p q) s t
  
  | F_ChoiceL : p : stmt -> q : stmt -> s : ok_state -> t : state ->
    footprint p s t ->
    footprint (Choice p q) s t
  
  | F_ChoiceR : p : stmt -> q : stmt -> s : ok_state -> t : state ->
    footprint q s t ->
    footprint (Choice p q) s t
  
  | F_Kleene0 : st : store -> p : stmt ->
    footprint (Kleene p) (st, empty_heap, Ok) (st, empty_heap, Ok)
  
  | F_KleeneS : p : stmt -> s : ok_state -> t : state ->
    footprint (Seq (Kleene p) p) s t ->
    footprint (Kleene p) s t
  
  | F_AllocFresh : st : store -> x : var -> l : loc { l =!= 0 } -> v : value ->
    footprint (Alloc x) (st, empty_heap, Ok) 
    (override st x (Loc l), singleton_full_heap l v, Ok)
  
  | F_AllocReuse : st : store -> x : var -> l : loc { l =!= 0 } -> v : value ->
    footprint (Alloc x) (st, singleton_empty_heap l, Ok)
    (override st x (Loc l), singleton_full_heap l v, Ok)
  
  | F_Free : st : store -> e : expr -> l : loc { l =!= 0 } -> v : value ->
    #(squash (eval_expr' st e == l)) ->
    footprint (Free e) (st, singleton_full_heap l v, Ok)
    (st, singleton_empty_heap l, Ok)
  
  | F_FreeEr : st : store -> e : expr -> l : loc { l =!= 0 } ->
    #(squash (eval_expr' st e == l)) ->
    footprint (Free e) (st, singleton_empty_heap l, Ok)
    (st, singleton_empty_heap l, Er)
  
  | F_FreeNull : st : store -> e : expr ->
    #(squash (eval_expr' st e == 0)) ->
    footprint (Free e) (st, empty_heap, Ok) (st, empty_heap, Er)
  
  | F_Load : st : store -> x : var -> e : expr -> l : loc { l =!= 0 } -> v : value ->
    #(squash (eval_expr' st e == l)) ->
    footprint (Load x e) (st, singleton_full_heap l v, Ok)
    (override st x v, singleton_full_heap l v, Ok)
  
  | F_LoadEr : st : store -> x : var -> e : expr -> l : loc { l =!= 0 } ->
    #(squash (eval_expr' st e == l)) ->
    footprint (Load x e) (st, singleton_empty_heap l, Ok)
    (st, singleton_empty_heap l, Er)
  
  | F_LoadNull : st : store -> x : var -> e : expr ->
    #(squash (eval_expr' st e == 0)) ->
    footprint (Load x e) (st, empty_heap, Ok) (st, empty_heap, Er)
  
  | F_Store : st : store -> e1 : expr -> e2 : expr -> l : loc { l =!= 0 } -> v : value ->
    #(squash (eval_expr' st e1 == l)) ->
    footprint (Store e1 e2) (st, singleton_full_heap l v, Ok)
    (st, singleton_full_heap l (eval_value st e2), Ok)
  
  | F_StoreEr : st : store -> e1 : expr -> e2 : expr -> l : loc { l =!= 0 } ->
    #(squash (eval_expr' st e1 == l)) ->
    footprint (Store e1 e2) (st, singleton_empty_heap l, Ok)
    (st, singleton_empty_heap l, Er)
  
  | F_StoreNull : st : store -> e1 : expr -> e2 : expr ->
    #(squash (eval_expr' st e1 == 0)) ->
    footprint (Store e1 e2) (st, empty_heap, Ok) (st, empty_heap, Er)

// ============================================================
// 8. Soundness de footprints
// ============================================================

let rec footprint_sound (p : stmt) (s0 : state) (s1 : state) (f : footprint p s0 s1) 
  : GTot (runsto p s0 s1) (decreases f) =
  match f with
  | F_Skip st ->
    R_Skip (st, empty_heap, Ok)

  | F_Assign st x e ->
    R_Assign x e (st, empty_heap, Ok)

  | F_Nondet st x v ->
    R_Nondet (st, empty_heap, Ok) #x v

  | F_Assume st e ->
    R_Assume (st, empty_heap, Ok) #e ()

  | F_Error st ->
    R_Error (st, empty_heap, Ok)
  
  | F_Seq p q st0 stm st1 h_common h_p h_q h0 h1 m1 f_p f_q ->
    let r_p = 
      footprint_sound p (st0, h0, Ok) (stm, h_common <+> h_p, Ok) f_p
    in
    let r_q =
      footprint_sound q (stm, h_common <+> h_q, Ok) (st1, h1, m1) f_q
    in
    let r_p_framed = r_frame r_p h_q #() #() in
    let r_q_framed = r_frame r_q h_p #() #() in
    let s_mid_p = (stm, (h_common <+> h_p) <+> h_q, Ok) in
    let s_mid_q = (stm, (h_common <+> h_q) <+> h_p, Ok) in
    let s_final = (st1, h1 <+> h_p, m1) in
    state_equiv_eq s_mid_q s_mid_p;
    R_Seq #p #q #(st0, h0 <+> h_q, Ok) #s_mid_p #s_final r_p_framed r_q_framed
  
  | F_SeqEr p q s t f_p ->
    let r_p = footprint_sound p s t f_p in
    R_SeqEr #p #q #s #t r_p

  | F_ChoiceL p q s t f_p ->
    let r_p = footprint_sound p s t f_p in
    R_ChoiceL #p #q #s #t r_p
  
  | F_ChoiceR p q s t f_q ->
    let r_q = footprint_sound q s t f_q in
    R_ChoiceR #p #q #s #t r_q
  
  | F_Kleene0 st p ->
    R_Kleene0 #p #(st, empty_heap, Ok)

  | F_KleeneS p s t f_p ->
    let r_p = footprint_sound (Seq (Kleene p) p) s t f_p in
    R_KleeneS #p #s #t r_p

  | F_AllocFresh st x l v ->
    let s0 = (st, empty_heap, Ok) in
    let s1 = (override st x (Loc l), singleton_full_heap l v, Ok) in
    let r = R_Alloc s0 #x l v in
    state_equiv_eq (override st x (Loc l), override s0._2 l (Full v), Ok) s1;
    r

  | F_AllocReuse st x l v ->
    let s0 = (st, singleton_empty_heap l, Ok) in
    let s1 = (override st x (Loc l), singleton_full_heap l v, Ok) in
    let r = R_Alloc s0 #x l v in
    state_equiv_eq (override st x (Loc l), override s0._2 l (Full v), Ok) s1;
    r

  | F_Free st e l v ->
    let s0 = (st, singleton_full_heap l v, Ok) in
    let s1 = (st, override (singleton_full_heap l v) l Empty, Ok) in
    let r = R_Free s0 e l v in
    state_equiv_eq s1 (st, singleton_empty_heap l, Ok);
    r

  | F_FreeEr st e l ->
    R_FreeEr (st, singleton_empty_heap l, Ok) e

  | F_FreeNull st e ->
    R_FreeNull (st, empty_heap, Ok) e

  | F_Load st x e l v -> 
    R_Load (st, singleton_full_heap l v, Ok) x e v

  | F_LoadEr st x e l ->
    R_LoadEr (st, singleton_empty_heap l, Ok) x e

  | F_LoadNull st x e ->
    R_LoadNull (st, empty_heap, Ok) x e

  | F_Store st e1 e2 l v ->
    let s0 = (st, singleton_full_heap l v, Ok) in
    let s1 = (st, override (singleton_full_heap l v) l (Full (eval_value st e2)), Ok) in
    let r = R_Store s0 e1 e2 l v in
    state_equiv_eq s1 (st, singleton_full_heap l (eval_value st e2), Ok);
    r

  | F_StoreEr st e1 e2 l ->
    R_StoreEr (st, singleton_empty_heap l, Ok) e1 e2

  | F_StoreNull st e1 e2 ->
    R_StoreNull (st, empty_heap, Ok) e1 e2

// ============================================================
// 9. Clausura por marcos de footprints
// ============================================================

noeq
type framed_footprint : stmt -> state -> state -> Type0 =
  | FF_Frame : p : stmt -> s0 : state -> s1 : state -> h_fr : heap ->
    fp : footprint p s0 s1 -> 
    d0 : squash (s0._2 >< h_fr) ->
    d1 : squash (s1._2 >< h_fr) ->
    framed_footprint p (s0._1, s0._2 <+> h_fr, s0._3) (s1._1, s1._2 <+> h_fr, s1._3)

let framed_footprint_sound (p : stmt) (s0 : state) (s1 : state) (ff : framed_footprint p s0 s1)
  : GTot (runsto p s0 s1) (decreases ff) =
  match ff with
  | FF_Frame p s0 s1 h_fr f_p _ _ ->
    let r_p = footprint_sound p s0 s1 f_p in
    r_frame r_p h_fr #() #()

// ============================================================
// 10. Lemas auxiliares para cross-split y descomposición
// ============================================================

let footprint_starts_ok (#p : stmt) (#s0 #s1 : state) (fp : footprint p s0 s1)
  : Lemma (ensures s0._3 == Ok) =
  match fp with
  | _ -> ()

let cell_meet (c1 c2 : cell) : cell =
  match c1, c2 with
  | Unknown, _ -> Unknown
  | _, Unknown -> Unknown
  | _, _ -> c1

let cross_heap (h1 h2 : heap) : heap =
  on loc (fun l -> cell_meet (h1 l) (h2 l))

let cell_cross_split (c1 c2 c3 c4 : cell)
  : Lemma (requires cell_disjoint c1 c2 /\
            cell_disjoint c3 c4 /\
            cell_merge c1 c2 == cell_merge c3 c4)
          (ensures (
            let c13 = cell_meet c1 c3 in
            let c14 = cell_meet c1 c4 in
            let c23 = cell_meet c2 c3 in
            let c24 = cell_meet c2 c4 in
            cell_disjoint c13 c14 /\
            cell_disjoint c13 c23 /\
            cell_disjoint c13 c24 /\
            cell_disjoint c14 c23 /\
            cell_disjoint c14 c24 /\
            cell_disjoint c23 c24 /\
            cell_merge c13 c14 == c1 /\
            cell_merge c23 c24 == c2 /\
            cell_merge c13 c23 == c3 /\
            cell_merge c14 c24 == c4
          )) =
  ()

let heaps_pairwise_disjoint (h13 h14 h23 h24 : heap) : prop =
  h13 >< h14 /\
  h13 >< h23 /\
  h13 >< h24 /\
  h14 >< h23 /\
  h14 >< h24 /\
  h23 >< h24

noeq
type cross_split_witness (h1 h2 h3 h4 : heap) = {
  h13 : heap; h14 : heap; h23 : heap; h24 : heap;
  pairwise_disjoint : squash (heaps_pairwise_disjoint h13 h14 h23 h24);
  split_h1 : squash (forall l. heap_merge h13 h14 l == h1 l);
  split_h2 : squash (forall l. heap_merge h23 h24 l == h2 l);
  split_h3 : squash (forall l. heap_merge h13 h23 l == h3 l);
  split_h4 : squash (forall l. heap_merge h14 h24 l == h4 l)
}

let heap_cross_split (h1 h2 h3 h4 : heap)
  (#_ : squash (h1 >< h2)) (#_ : squash (h3 >< h4))
  (#_ : squash (forall l. heap_merge h1 h2 l == heap_merge h3 h4 l))
  : GTot (cross_split_witness h1 h2 h3 h4) =
  let h13 = cross_heap h1 h3 in
  let h14 = cross_heap h1 h4 in
  let h23 = cross_heap h2 h3 in
  let h24 = cross_heap h2 h4 in

  let pointwise (l : loc)
    : Lemma 
      (ensures (
        let c13 = h13 l in
        let c14 = h14 l in
        let c23 = h23 l in
        let c24 = h24 l in
        cell_disjoint c13 c14 /\
        cell_disjoint c13 c23 /\
        cell_disjoint c13 c24 /\
        cell_disjoint c14 c23 /\
        cell_disjoint c14 c24 /\
        cell_disjoint c23 c24 /\
        cell_merge c13 c14 == h1 l /\
        cell_merge c23 c24 == h2 l /\
        cell_merge c13 c23 == h3 l /\
        cell_merge c14 c24 == h4 l
      )) =
    cell_cross_split (h1 l) (h2 l) (h3 l) (h4 l)
  in
  {
    h13 = h13; h14 = h14; h23 = h23; h24 = h24;
    pairwise_disjoint = ();
    split_h1 = (); split_h2 = ();
    split_h3 = (); split_h4 = ()
  }

noeq
type frame_parts (p : stmt) (s0 : state) (s1 : state) = {
  local_start : state; local_end : state; frame_heap : heap;
  local_footprint : footprint p local_start local_end;
  frame_disjoint_start : squash (local_start._2 >< frame_heap);
  frame_disjoint_end : squash (local_end._2 >< frame_heap);
  rebuild_start : squash (state_equiv
    (local_start._1, local_start._2 <+> frame_heap, local_start._3) s0);
  rebuild_end : squash (state_equiv
    (local_end._1, local_end._2 <+> frame_heap, local_end._3) s1)
}

let flatten_framed (#p : stmt) (#s0 #s1 : state) (ff : framed_footprint p s0 s1)
  : GTot (frame_parts p s0 s1) (decreases ff) =
  match ff with
  | FF_Frame _ sl0 sl1 h_fr fp d0 d1 ->
    {
      local_start = sl0; local_end = sl1; 
      frame_heap = h_fr; local_footprint = fp;
      frame_disjoint_start = d0;
      frame_disjoint_end = d1;
      rebuild_start = (); rebuild_end = ()
    }

let map_framed_footprint (#p #q : stmt) (#s0 #s1 : state)
  (transform : (#sl0 : state -> #sl1 : state -> footprint p sl0 sl1 -> GTot (footprint q sl0 sl1)))
  (ff : framed_footprint p s0 s1)
  : GTot (framed_footprint q s0 s1) (decreases ff) =
  match ff with
  | FF_Frame _ s0_local s1_local h_fr fp d0 d1 ->
    let fp' = transform fp in
    FF_Frame q s0_local s1_local h_fr fp' d0 d1

let framed_seq_er (#p #q : stmt) (#s0 : state) (#s1 : state { s1._3 == Er })
  (ff  : framed_footprint p s0 s1)
  : GTot (framed_footprint (Seq p q) s0 s1) (decreases ff) =
  match ff with
  | FF_Frame _ s0_local s1_local h_fr fp_p d0 d1 ->
    footprint_starts_ok fp_p;
    let fp_seq = F_SeqEr p q s0_local s1_local fp_p in
    FF_Frame (Seq p q) s0_local s1_local h_fr fp_seq d0 d1

// ============================================================
// 11. Completitud de la descomposición en huellas
// ============================================================

let frame_local (#p : stmt) (#t0 #t1 : state) (fp : footprint p t0 t1)
  (s0 s1 : state) (h_fr : heap)
  (#_ : squash (t0._2 >< h_fr /\ t1._2 >< h_fr /\
                state_equiv (t0._1, t0._2 <+> h_fr, t0._3) s0 /\
                state_equiv (t1._1, t1._2 <+> h_fr, t1._3) s1))
  : GTot (framed_footprint p s0 s1) =
  state_equiv_eq (t0._1, t0._2 <+> h_fr, t0._3) s0;
  state_equiv_eq (t1._1, t1._2 <+> h_fr, t1._3) s1;
  FF_Frame p t0 t1 h_fr fp () ()

let rec runsto_decompose (#p : stmt) (#s0 #s1 : state) (r : runsto p s0 s1)
  : GTot (framed_footprint p s0 s1) (decreases r) =
  match r with
  | R_Skip s -> frame_local (F_Skip s._1) s0 s1 s._2

  | R_Error s -> frame_local (F_Error s._1) s0 s1 s._2
  
  | R_Assign x e s -> frame_local (F_Assign s._1 x e) s0 s1 s._2
  
  | R_Nondet s #x v -> frame_local (F_Nondet s._1 x v) s0 s1 s._2
  
  | R_Assume s #e _ -> frame_local (F_Assume s._1 e) s0 s1 s._2
  
  | R_SeqEr #p #q #s #t r_p ->
    let ff_p = runsto_decompose r_p in
    framed_seq_er #p #q #s #t ff_p
  
  | R_Seq #p #q #s #t #u r_p r_q ->
    let ff_p = runsto_decompose r_p in
    let ff_q = runsto_decompose r_q in
    let parts_p = flatten_framed ff_p in
    let parts_q = flatten_framed ff_q in
    let p0 = parts_p.local_start in
    let p1 = parts_p.local_end in
    let fr_p = parts_p.frame_heap in
    let fp_p = parts_p.local_footprint in
    let dp1 = parts_p.frame_disjoint_end in
    let q0 = parts_q.local_start in
    let q1 = parts_q.local_end in
    let fr_q = parts_q.frame_heap in
    let fp_q = parts_q.local_footprint in
    let dq0 = parts_q.frame_disjoint_start in
    let p_mid = (p1._1, p1._2 <+> fr_p, p1._3) in
    let q_mid = (q0._1, q0._2 <+> fr_q, q0._3) in
    let cs = heap_cross_split p1._2 fr_p q0._2 fr_q #dp1 #dq0 #() in
    let h_common = cs.h13 in
    let h_p = cs.h14 in
    let h_q = cs.h23 in
    let h_ext = cs.h24 in
    let p0_aligned = (p0._1, p0._2, Ok) in
    let p1_aligned = (p1._1, h_common <+> h_p, Ok) in
    let q0_aligned = (p1._1, h_common <+> h_q, Ok) in
    let q1_aligned = (q1._1, q1._2, q1._3) in
    state_equiv_eq p0 p0_aligned;
    state_equiv_eq p1 p1_aligned;
    state_equiv_eq q0 q0_aligned;
    state_equiv_eq q1 q1_aligned;
    let seq0_local = (p0._1, p0._2 <+> h_q, Ok) in
    let seq1_local = (q1._1, q1._2 <+> h_p, q1._3) in
    let fp_seq = F_Seq p q p0._1 p1._1 q1._1 h_common h_p h_q p0._2 q1._2 q1._3 fp_p fp_q in
    let seq0_framed = (p0._1, (p0._2 <+> h_q) <+> h_ext, Ok) in
    let seq1_framed = (q1._1, (q1._2 <+> h_p) <+> h_ext, q1._3) in
    let ff_seq = FF_Frame (Seq p q) seq0_local seq1_local h_ext fp_seq () () in
    let p0_framed = (p0._1, p0._2 <+> fr_p, Ok) in
    let q1_framed = (q1._1, q1._2 <+> fr_q, q1._3) in
    state_equiv_eq seq0_framed s;
    state_equiv_eq seq1_framed u;
    ff_seq
  
  | R_ChoiceL #p #q r_p ->
    let ff_p = runsto_decompose r_p in
    map_framed_footprint (fun #sl0 #sl1 fp_p ->
      footprint_starts_ok fp_p;
      F_ChoiceL p q sl0 sl1 fp_p) ff_p
  
  | R_ChoiceR #p #q r_q ->
    let ff_q = runsto_decompose r_q in
    map_framed_footprint (fun #sl0 #sl1 fp_q ->
      footprint_starts_ok fp_q;
      F_ChoiceR p q sl0 sl1 fp_q) ff_q
  
  | R_Kleene0 #p #s -> frame_local (F_Kleene0 s._1 p) s0 s1 s._2
  
  | R_KleeneS #p #s #t r_seq ->
    let ff_seq = runsto_decompose r_seq in
    map_framed_footprint (fun #sl0 #sl1 fp_seq ->
      footprint_starts_ok fp_seq;
      F_KleeneS p sl0 sl1 fp_seq) ff_seq
  
  | R_Alloc s #x l v ->
    if Unknown? (s._2 l) then
      frame_local (F_AllocFresh s._1 x l v) s0 s1 (heap_without s._2 l)
    else
      frame_local (F_AllocReuse s._1 x l v) s0 s1 (heap_without s._2 l)
  
  | R_Free s e l v -> frame_local (F_Free s._1 e l v) s0 s1 (heap_without s._2 l)
  
  | R_FreeEr s e ->
    let l = eval_expr s e in
    frame_local (F_FreeEr s._1 e l) s0 s1 (heap_without s._2 l)
  
  | R_FreeNull s e -> frame_local (F_FreeNull s._1 e) s0 s1 s._2
  
  | R_Load s x e v ->
    let l = eval_expr s e in
    frame_local (F_Load s._1 x e l v) s0 s1 (heap_without s._2 l)
  
  | R_LoadEr s x e ->
    let l = eval_expr s e in
    frame_local (F_LoadEr s._1 x e l) s0 s1 (heap_without s._2 l)
  
  | R_LoadNull s x e -> frame_local (F_LoadNull s._1 x e) s0 s1 s._2
  
  | R_Store s e1 e2 l v -> frame_local (F_Store s._1 e1 e2 l v) s0 s1 (heap_without s._2 l)

  | R_StoreEr s e1 e2 ->
    let l = eval_expr s e1 in
    frame_local (F_StoreEr s._1 e1 e2 l) s0 s1 (heap_without s._2 l)
  
  | R_StoreNull s e1 e2 -> frame_local (F_StoreNull s._1 e1 e2) s0 s1 s._2
 
let framed_decomposition_sound (#p : stmt) (#s0 #s1 : state) (ff : framed_footprint p s0 s1)
  : GTot (runsto p s0 s1) =
  framed_footprint_sound p s0 s1 ff

let framed_decomposition_complete (#p : stmt) (#s0 #s1 : state) (r : runsto p s0 s1)
  : GTot (framed_footprint p s0 s1) =
  runsto_decompose r

// ============================================================
// 12. Orden por marcos y minimalidad
// ============================================================

let runs (p : stmt) (s0 s1 : state) : prop = exists (_ : runsto p s0 s1). True

let known (c : cell) : bool = not (Unknown? c)
let nonempty (h : heap) : prop = exists l. known (h l)

let framed_by (t0 t1 s0 s1 : state) (hf : heap) : prop =
  t0._2 >< hf /\ t1._2 >< hf /\
  s0 == (t0._1, t0._2 <+> hf, t0._3) /\
  s1 == (t1._1, t1._2 <+> hf, t1._3)

let minimal (p : stmt) (s0 s1 : state) : prop =
  runs p s0 s1 /\
  (forall (t0 t1 : state) (hf : heap).
    (runs p t0 t1 /\ nonempty hf /\ framed_by t0 t1 s0 s1 hf) ==> False)

let has_min_below (p : stmt) (s0 s1 : state) : prop =
  exists (t0 t1 : state) (hf : heap).
    minimal p t0 t1 /\ framed_by t0 t1 s0 s1 hf

// ============================================================
// 13. Cota
// ============================================================

let bounded (h : heap) (n : nat) : prop =
  forall (l : loc). l >= n ==> h l == Unknown

let rec count (h : heap) (n : nat) : GTot nat (decreases n) =
  if n = 0 then 0
  else count h (n - 1) + (
    if known (h (n - 1)) then 1 else 0
  )

let rec count_mono (h h' : heap) (n : nat)
  : Lemma (requires forall (l : loc). l < n /\ known (h l) ==> known (h' l))
          (ensures count h n <= count h' n) (decreases n) =
  if n = 0 then () else count_mono h h' (n - 1)

let rec count_strict (h h' : heap) (n : nat) (l : loc)
  : Lemma (requires (forall (l' : loc). l' < n /\ known (h l') ==> known (h' l')) /\
            l < n /\ known (h' l) /\ not (known (h l)))
          (ensures count h n < count h' n) (decreases n) =
  if l = n - 1 then count_mono h h' (n - 1)
  else count_strict h h' (n - 1) l

let union_bounded (h1 h2 : heap) (n1 n2 : nat)
  : Lemma (requires h1 >< h2 /\ bounded h1 n1 /\ bounded h2 n2)
          (ensures bounded (h1 <+> h2) (if n1 >= n2 then n1 else n2)) =
  ()

let rec footprint_bounded (#p : stmt) (#s0 #s1 : state) (f : footprint p s0 s1)
  : Lemma (ensures exists (n : nat). bounded s0._2 n) (decreases f) =
  match f with
  | F_Seq p q st0 stm st1 h_common h_p h_q h0 h1 m1 f_p f_q ->
    footprint_bounded f_p;
    footprint_bounded f_q;
    let n0 = indefinite_description_ghost nat (fun n -> bounded h0 n) in
    let nq = indefinite_description_ghost nat (fun n -> bounded (h_common <+> h_q) n) in
    union_bounded h0 h_q n0 nq
  | F_SeqEr _ _ _ _ f' -> footprint_bounded f'
  | F_ChoiceL _ _ _ _ f' -> footprint_bounded f'
  | F_ChoiceR _ _ _ _ f' -> footprint_bounded f'
  | F_KleeneS _ _ _ f' -> footprint_bounded f'
  | F_AllocReuse _ _ l _ -> assert (bounded s0._2 (l + 1))
  | F_Free _ _ l _ -> assert (bounded s0._2 (l + 1))
  | F_FreeEr _ _ l -> assert (bounded s0._2 (l + 1))
  | F_Load _ _ _ l _ -> assert (bounded s0._2 (l + 1))
  | F_LoadEr _ _ _ l -> assert (bounded s0._2 (l + 1))
  | F_Store _ _ _ l _ -> assert (bounded s0._2 (l + 1))
  | F_StoreEr _ _ _ l -> assert (bounded s0._2 (l + 1))
  | _ -> assert (bounded s0._2 0)

// ============================================================
// 14. Composición de marcos
// ============================================================

let compose_frames (r0 r1 t0 t1 s0 s1 : state) (hf1 hf2 : heap)
  : Lemma (requires framed_by r0 r1 t0 t1 hf1 /\ framed_by t0 t1 s0 s1 hf2)
          (ensures hf1 >< hf2 /\ framed_by r0 r1 s0 s1 (hf1 <+> hf2)) =
  state_equiv_eq (r0._1, r0._2 <+> (hf1 <+> hf2), r0._3) s0;
  state_equiv_eq (r1._1, r1._2 <+> (hf1 <+> hf2), r1._3) s1

let empty_frame (s0 s1 : state)
  : Lemma (framed_by s0 s1 s0 s1 empty_heap) =
  state_equiv_eq (s0._1, s0._2 <+> empty_heap, s0._3) s0;
  state_equiv_eq (s1._1, s1._2 <+> empty_heap, s1._3) s1

// ============================================================
// 15. Existe una transición minimal
// ============================================================

let rec minimize (p : stmt) (s0 s1 : state) (n : nat)
  : Lemma (requires runs p s0 s1 /\ bounded s0._2 n)
          (ensures has_min_below p s0 s1) (decreases (count s0._2 n)) =
  empty_frame s0 s1;
  if t2b (minimal p s0 s1) then ()
  else
    let t0 = indefinite_description_ghost state (fun t0 ->
      exists (t1 : state) (hf : heap).
        runs p t0 t1 /\ nonempty hf /\ framed_by t0 t1 s0 s1 hf) in
    let t1 = indefinite_description_ghost state (fun t1 ->
      exists (hf : heap).
        runs p t0 t1 /\ nonempty hf /\ framed_by t0 t1 s0 s1 hf) in
    let hf = indefinite_description_ghost heap (fun hf ->
      runs p t0 t1 /\ nonempty hf /\ framed_by t0 t1 s0 s1 hf) in
    let l = indefinite_description_ghost loc (fun l -> known (hf l)) in
    count_strict t0._2 s0._2 n l;
    minimize p t0 t1 n;
    let r0 = indefinite_description_ghost state (fun r0 ->
      exists (r1 : state) (hr : heap).
        minimal p r0 r1 /\ framed_by r0 r1 t0 t1 hr) in
    let r1 = indefinite_description_ghost state (fun r1 ->
      exists (hr : heap).
        minimal p r0 r1 /\ framed_by r0 r1 t0 t1 hr) in
    let hr = indefinite_description_ghost heap (fun hr ->
      minimal p r0 r1 /\ framed_by r0 r1 t0 t1 hr) in
    compose_frames r0 r1 t0 t1 s0 s1 hr hf

// ============================================================
// 16. Teorema de la huella
// ============================================================

let footprint_theorem_minimal (#p : stmt) (#s0 #s1 : state) (r : runsto p s0 s1)
  : Lemma (has_min_below p s0 s1) =
  let parts = flatten_framed (runsto_decompose r) in
  let t0 = parts.local_start in
  let t1 = parts.local_end in
  let hf = parts.frame_heap in
  footprint_bounded parts.local_footprint;
  state_equiv_eq (t0._1, t0._2 <+> hf, t0._3) s0;
  state_equiv_eq (t1._1, t1._2 <+> hf, t1._3) s1;
  let r_loc = footprint_sound p t0 t1 parts.local_footprint in
  exists_intro (fun (_ : runsto p t0 t1) -> True) r_loc;
  let n = indefinite_description_ghost nat (fun n -> bounded t0._2 n) in
  minimize p t0 t1 n;
  let r0 = indefinite_description_ghost state (fun r0 ->
    exists (r1 : state) (hr : heap).
      minimal p r0 r1 /\ framed_by r0 r1 t0 t1 hr) in
  let r1 = indefinite_description_ghost state (fun r1 ->
    exists (hr : heap).
      minimal p r0 r1 /\ framed_by r0 r1 t0 t1 hr) in
  let hr = indefinite_description_ghost heap (fun hr ->
    minimal p r0 r1 /\ framed_by r0 r1 t0 t1 hr) in
  compose_frames r0 r1 t0 t1 s0 s1 hr hf

let minimal_framed_runs (p : stmt) (r0 r1 : state) (hf : heap)
  : Lemma (requires minimal p r0 r1 /\ r0._2 >< hf /\ r1._2 >< hf)
          (ensures runs p (r0._1, r0._2 <+> hf, r0._3) (r1._1, r1._2 <+> hf, r1._3)) =
  let r = indefinite_description_ghost (runsto p r0 r1) (fun _ -> True) in
  exists_intro (fun (_ : runsto p (r0._1, r0._2 <+> hf, r0._3) (r1._1, r1._2 <+> hf, r1._3)) -> True)
    (r_frame r hf #() #())

// ============================================================
// 17. Adecuación a heaps completos
// ============================================================

let complete_cell (c : cell) : cell =
  match c with
  | Unknown -> Empty
  | _ -> c

let complete (h : heap) : heap = on loc (fun l -> complete_cell (h l))

let cstate (s : state) : state = (s._1, complete s._2, s._3)

let complete_override (st : store) (h : heap) (m : term_mode)
  (l : loc) (c : cell { known c })
  : Lemma ((st, complete (override h l c), m) == (st, override (complete h) l c, m)) =
  state_equiv_eq (st, complete (override h l c), m) (st, override (complete h) l c, m)

let rec run_complete (#p : stmt) (#s0 #s1 : state) (r : runsto p s0 s1)
  : GTot (runsto p (cstate s0) (cstate s1)) (decreases r) =
  let c0 = cstate s0 in
  match r with
  | R_Skip _ -> R_Skip c0
  | R_Error _ -> R_Error c0
  | R_Assign x e _ -> R_Assign x e c0
  | R_Nondet _ #x v -> R_Nondet c0 #x v
  | R_Assume _ #e _ -> R_Assume c0 #e ()
  | R_SeqEr #p #q r_p ->
    R_SeqEr #p #q #c0 #(cstate s1) (run_complete r_p)
  | R_Seq #p #q #s #t r_p r_q ->
    R_Seq #p #q #c0 #(cstate t) #(cstate s1) (run_complete r_p) (run_complete r_q)
  | R_ChoiceL #p #q r_p ->
    R_ChoiceL #p #q #c0 #(cstate s1) (run_complete r_p)
  | R_ChoiceR #p #q r_q ->
    R_ChoiceR #p #q #c0 #(cstate s1) (run_complete r_q)
  | R_Kleene0 #p -> R_Kleene0 #p #c0
  | R_KleeneS #p r_seq ->
    R_KleeneS #p #c0 #(cstate s1) (run_complete r_seq)
  | R_Alloc _ #x l v ->
    complete_override s1._1 s0._2 s1._3 l (Full v);
    R_Alloc c0 #x l v
  | R_Free _ e l v ->
    complete_override s1._1 s0._2 s1._3 l Empty;
    R_Free c0 e l v
  | R_FreeEr _ e -> R_FreeEr c0 e
  | R_FreeNull _ e -> R_FreeNull c0 e
  | R_Load _ x e v -> R_Load c0 x e v
  | R_LoadEr _ x e -> R_LoadEr c0 x e
  | R_LoadNull _ x e -> R_LoadNull c0 x e
  | R_Store _ e1 e2 l v ->
    complete_override s1._1 s0._2 s1._3 l (Full (eval_value s0._1 e2));
    R_Store c0 e1 e2 l v
  | R_StoreEr _ e1 e2 -> R_StoreEr c0 e1 e2
  | R_StoreNull _ e1 e2 -> R_StoreNull c0 e1 e2

// ============================================================
// 18. Certificado de existencia de error
// ============================================================

let no_alloc : cond =
  fun s -> forall l. s._2 l == Empty \/ s._2 l == Unknown

let rest (h : heap) : heap =
  on loc (fun l -> if Unknown? (h l) then Empty else Unknown)

let complete_split (h : heap)
  : Lemma (h >< rest h /\ complete h == (h <+> rest h)) =
  extensionality loc (fun _ -> cell) (complete h) (h <+> rest h)

let complete_sat (pre : cond) (s : state)
  : Lemma (requires pre s)
          (ensures (pre ** no_alloc) (cstate s)) =
  complete_split s._2;
  introduce_frame pre no_alloc (cstate s) s._2 (rest s._2)

let error_reachable (pre : cond) (p : stmt) : prop =
  exists (s0 s1 : state). pre s0 /\ s1._3 == Er /\ runs p s0 s1 /\
    (pre ** no_alloc) (cstate s0) /\
    (cstate s1)._3 == Er /\ runs p (cstate s0) (cstate s1)

let certify (#pre #post : cond) (#p : stmt)
  (pf : isl_triple pre p post) (s1 : state)
  : Lemma (requires post s1 /\ s1._3 == Er)
          (ensures error_reachable pre p) =
  let (| s0, r |) = soundness p pre post pf s1 in
  complete_sat pre s0;
  exists_intro (fun (_ : runsto p s0 s1) -> True) r;
  exists_intro (fun (_ : runsto p (cstate s0) (cstate s1)) -> True)
    (run_complete r);
  assert (pre s0 /\ s1._3 == Er /\ runs p s0 s1 /\
    (pre ** no_alloc) (cstate s0) /\
    (cstate s1)._3 == Er /\ runs p (cstate s0) (cstate s1))
