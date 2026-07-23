module IncSepLogicOne

open FStar.Classical

// ============================================================
// 1. Syntax and states
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

type store = var -> value
type heap = loc -> cell

let heap_is_complete (h : heap) : prop =
  forall l. ~(Unknown? (h l))

let complete_heap : Type = h : heap { heap_is_complete h }

let initial_heap : complete_heap =
  fun _ -> Empty

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

let override (#a : eqtype) (#b : Type) (f : a -> b) (x : a) (y : b) : a -> b =
  fun z -> if z = x then y else f z

unfold let state_equiv (s1 s2 : state) : prop =
  (forall x. s1._1 x == s2._1 x) /\
  (forall l. s1._2 l == s2._2 l) /\
  s1._3 == s2._3

// ============================================================
// 2. Heap model and heap algebra
// ============================================================

let cell_disjoint (c1 c2 : cell) : prop =
  c1 == Unknown \/ c2 == Unknown

let cell_union (c1 c2 : cell { cell_disjoint c1 c2 }) : cell =
  match c1 with
    | Unknown -> c2
    | _ -> c1

let heaps_disjoint (h1 h2 : heap) : prop =
  forall l. cell_disjoint (h1 l) (h2 l)

let heap_union (h1 h2 : heap { heaps_disjoint h1 h2 }) : heap =
  fun l -> cell_union (h1 l) (h2 l)

let empty_heap : heap = fun _ -> Unknown

let singleton_empty_heap (l : loc) : heap =
  fun l' -> if l' = l then Empty else Unknown

let singleton_full_heap (l : loc) (v : value) : heap =
  fun l' -> if l' = l then Full v else Unknown

let heap_without (h : heap) (l : loc) : heap =
  fun l' ->
    if l' = l then Unknown
    else h l'

// ============================================================
// 3. Operational semantics
// ============================================================

noeq
type runsto : (p : stmt) -> (s0 : state) -> (s1 : state) -> Type0 =
  | R_Ext : #p : stmt -> #s0 : state -> #s1 : state ->
    runsto p s0 s1 -> s0' : state -> s1' : state ->
    (squash (state_equiv s0 s0')) ->
    (squash (state_equiv s1 s1')) ->
    runsto p s0' s1'

  | R_Skip : s : state { s._3 == Ok } -> 
    runsto Skip s s
  
  | R_Error : s : state { s._3 == Ok } -> 
    runsto Error s (s._1, s._2, Er)
  
  | R_Assign : x : var -> e : expr -> s : state { s._3 == Ok } -> 
    runsto (Assign x e) s (override s._1 x (Nat (eval_expr s e)), s._2, s._3)
  
  | R_Nondet : s : state { s._3 == Ok } -> #x : var -> v : value ->
    runsto (Nondet x) s (override s._1 x v, s._2, s._3)
  
  | R_Assume : s : state { s._3 == Ok } -> #e : expr -> 
    squash (eval_expr s e =!= 0) ->
    runsto (Assume e) s s
  
  | R_SeqEr : #p : stmt -> #q : stmt ->
    #s : state { s._3 == Ok } -> #t : state { t._3 == Er } ->
    runsto p s t -> 
    runsto (Seq p q) s t
  
  | R_Seq : #p : stmt -> #q : stmt ->
    #s : state { s._3 == Ok } -> #t : state { t._3 == Ok } -> #u : state ->
    runsto p s t -> runsto q t u ->
    runsto (Seq p q) s u
  
  | R_ChoiceL : #p : stmt -> #q : stmt ->
    #s : state { s._3 == Ok } -> #t : state ->
    runsto p s t -> runsto (Choice p q) s t
  
  | R_ChoiceR : #p : stmt -> #q : stmt ->
    #s: state { s._3 == Ok } -> #t : state ->
    runsto q s t -> runsto (Choice p q) s t
  
  | R_Kleene0 : #p : stmt -> #s : state { s._3 == Ok } -> 
    runsto (Kleene p) s s
  
  | R_KleeneS : #p : stmt -> #s : state { s._3 == Ok } -> #t : state ->
    runsto (Seq (Kleene p) p) s t ->
    runsto (Kleene p) s t

  | R_Alloc : s : state { s._3 == Ok } -> #x : var -> 
    l : loc { l =!= 0 } -> v : value ->
    #(squash (s._2 l == Unknown \/ s._2 l == Empty)) ->
    runsto (Alloc x) s (override s._1 x (Loc l), override s._2 l (Full v), s._3)
  
  | R_Free : s : state { s._3 == Ok } -> e : expr -> l : loc -> v : value ->
    #(squash (eval_expr s e == l /\ l =!= 0)) ->
    #(squash (s._2 l == Full v)) ->
    runsto (Free e) s (s._1, override s._2 l Empty, s._3)

  | R_FreeEr : s : state { s._3 == Ok } -> e : expr -> l : loc { l =!= 0 } ->
    #(squash (eval_expr s e == l)) ->
    #(squash (s._2 l == Empty)) ->
    runsto (Free e) s (s._1, s._2, Er)
  
  | R_FreeNull : s : state { s._3 == Ok } -> e : expr ->
    #(squash (eval_expr s e == 0)) ->
    runsto (Free e) s (s._1, s._2, Er)

  | R_Load : s : state { s._3 == Ok } -> x : var -> e : expr ->
    l : loc { l =!= 0 } -> v : value ->
    #(squash (s._2 l == Full v)) ->
    #(squash (eval_expr s e == l)) ->
    runsto (Load x e) s (override s._1 x v, s._2, s._3)

  | R_LoadEr : s : state { s._3 == Ok } -> x : var -> 
    e : expr -> l : loc { l =!= 0 } ->
    #(squash (eval_expr s e == l)) ->
    #(squash (s._2 l == Empty)) ->
    runsto (Load x e) s (s._1, s._2, Er)

  | R_LoadNull : s : state { s._3 == Ok } -> x : var -> e : expr ->
    #(squash (eval_expr s e == 0)) ->
    runsto (Load x e) s (s._1, s._2, Er)

  | R_Store : s : state { s._3 == Ok } -> e1 : expr -> e2 : expr ->
    l : loc { l =!= 0 } -> v : value ->
    #(squash (s._2 l == Full v)) ->
    #(squash (eval_expr s e1 == l)) ->
    runsto (Store e1 e2) s (s._1, override s._2 l (Full (Nat (eval_expr s e2))), s._3)

  | R_StoreEr : s : state { s._3 == Ok } -> e1 : expr ->
    e2 : expr -> l : loc { l =!= 0 } ->
    #(squash (eval_expr s e1 == l)) ->
    #(squash (s._2 l == Empty)) ->
    runsto (Store e1 e2) s (s._1, s._2, Er)
  
  | R_StoreNull : s : state { s._3 == Ok } -> e1 : expr -> e2 : expr ->
    #(squash (eval_expr s e1 == 0)) ->
    runsto (Store e1 e2) s (s._1, s._2, Er)

// ============================================================
// 4. Operational metatheory
// ============================================================

let match_except_vars (vars : string -> prop) (st1 st2 : store) : prop =
  forall x. ~(vars x) ==> st1 x == st2 x

let rec modifies (p : stmt) (x : var) : prop =
  match p with
  | Assign y _ -> x = y
  | Nondet y -> x = y
  | Seq s1 s2 -> modifies s1 x \/ modifies s2 x
  | Choice s1 s2 -> modifies s1 x \/ modifies s2 x
  | Kleene s -> modifies s x
  | Alloc y -> x = y
  | Load y _ -> x = y
  | _ -> False

let rec lemma_runsto_modifies (#p : stmt) (#s0 #s1 : state) (r : runsto p s0 s1) 
  : Lemma (ensures match_except_vars (modifies p) s0._1 s1._1)
          (decreases r)=
  match r with
  | R_Ext r' _ _ _ _ ->
    lemma_runsto_modifies r'
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
  Lemma (requires (let (_, hp1, _) = s1 in 
                   heaps_disjoint hp1 h_fr))
        (ensures (let (_, hp0, _) = s0 in
                  heaps_disjoint hp0 h_fr))
        (decreases r) 
  = match r with
  | R_Ext r' _ _ _ _ ->
    lemma_runsto_disjoint h_fr r'
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
  (#_ : squash (let (_, hp, _) = s0 in heaps_disjoint hp h_fr))
  (#_ : squash (let (_, hp, _) = s1 in heaps_disjoint hp h_fr)) :
  GTot (runsto p 
    (let (st, hp, m) = s0 in (st, heap_union hp h_fr, m))
    (let (st, hp, m) = s1 in (st, heap_union hp h_fr, m)))
  (decreases r) = 
  let (st0, hp0, m0) = s0 in
  let (st1, hp1, m1) = s1 in
  let s0_fr = (st0, heap_union hp0 h_fr, m0) in
  let s1_fr = (st1, heap_union hp1 h_fr, m1) in
  match r with
  | R_Ext r' _ _ _ _ ->
    let r_fr = r_frame r' h_fr #() #() in
    R_Ext r_fr s0_fr s1_fr () ()
  | R_Skip _ ->
    R_Ext (R_Skip s0_fr) s0_fr s1_fr () ()
  | R_Error _ ->
    R_Ext (R_Error s0_fr) s0_fr s1_fr () ()
  | R_Assign x e s ->
    R_Ext (R_Assign x e s0_fr) s0_fr s1_fr () ()
  | R_Nondet _ #x v ->
    R_Ext (R_Nondet s0_fr #x v) s0_fr s1_fr () ()
  | R_Assume _ #e _ ->
    R_Ext (R_Assume s0_fr #e ()) s0_fr s1_fr () ()
  | R_SeqEr #p #q r_p ->
    let r_p_fr = r_frame r_p h_fr #() #() in
    let r_seq_er = R_SeqEr #p #q #s0_fr #s1_fr r_p_fr in
    R_Ext r_seq_er s0_fr s1_fr () ()
  | R_Seq #p #q #s #t r_p r_q ->
    lemma_runsto_disjoint h_fr r_q;
    let r_p_fr = r_frame r_p h_fr #() #() in
    let r_q_fr = r_frame r_q h_fr #() #() in
    let (st_t, hp_t, m_t) = t in
    let s_mid_fr = (st_t, heap_union hp_t h_fr, m_t) in
    let r_seq = R_Seq #p #q #s0_fr #s_mid_fr #s1_fr r_p_fr r_q_fr in
    R_Ext r_seq s0_fr s1_fr () ()
  | R_ChoiceL #p #q r_p ->
    let r_p_fr = r_frame r_p h_fr #() #() in
    let r_choice_l = R_ChoiceL #p #q #s0_fr #s1_fr r_p_fr in
    R_Ext r_choice_l s0_fr s1_fr () ()
  | R_ChoiceR #p #q r_q ->
    let r_q_fr = r_frame r_q h_fr #() #() in
    let r_choice_r = R_ChoiceR #p #q #s0_fr #s1_fr r_q_fr in
    R_Ext r_choice_r s0_fr s1_fr () ()
  | R_Kleene0 #p ->
    R_Ext (R_Kleene0 #p #s0_fr) s0_fr s1_fr () ()
  | R_KleeneS #p r_seq ->
    let r_seq_fr = r_frame r_seq h_fr #() #() in
    let r_kleene = R_KleeneS #p #s0_fr #s1_fr r_seq_fr in
    R_Ext r_kleene s0_fr s1_fr () ()
  | R_Alloc _ #x l v ->
    R_Ext (R_Alloc s0_fr #x l v) s0_fr s1_fr () ()
  | R_Free s e l v ->
    R_Ext (R_Free s0_fr e l v) s0_fr s1_fr () ()
  | R_FreeEr s e l ->
    R_Ext (R_FreeEr s0_fr e l) s0_fr s1_fr () ()
  | R_FreeNull s e ->
    R_Ext (R_FreeNull s0_fr e) s0_fr s1_fr () ()
  | R_Load s x e l v ->
    R_Ext (R_Load s0_fr x e l v) s0_fr s1_fr () ()
  | R_LoadEr s x e l ->
    R_Ext (R_LoadEr s0_fr x e l) s0_fr s1_fr () ()
  | R_LoadNull s x e ->
    R_Ext (R_LoadNull s0_fr x e) s0_fr s1_fr () ()
  | R_Store s e1 e2 l v ->
    R_Ext (R_Store s0_fr e1 e2 l v) s0_fr s1_fr () ()
  | R_StoreEr s e1 e2 l ->
    R_Ext (R_StoreEr s0_fr e1 e2 l) s0_fr s1_fr () ()
  | R_StoreNull s e1 e2 ->
    R_Ext (R_StoreNull s0_fr e1 e2) s0_fr s1_fr () ()

// ============================================================
// 5. Incorrectness Separation Logic
// ============================================================

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
  fun (st, hp, m) ->
    forall l. hp l == Unknown

unfold
let sep_conj (p q : cond) : cond =
  fun (st, hp, m) -> 
    exists h1 h2.
      heaps_disjoint h1 h2 /\
      hp == heap_union h1 h2 /\
      p (st, h1, m) /\ q (st, h2, m)

unfold let ( ** ) = sep_conj

let independent_on_vars (vars : string -> prop) (c : cond) : prop =
  forall (st1 st2 : store) (hp : heap) (m1 m2 : term_mode).
    match_except_vars vars st1 st2 ==> (c (st1, hp, m1) <==> c (st2, hp, m2))

unfold let is_ok (c : cond) : cond = fun s -> c s /\ s._3 == Ok

unfold
let kleene_pre (variant : nat -> cond) : cond =
  is_ok (variant 0)

unfold
let kleene_post (variant : nat -> cond) : cond =
  fun s -> exists (n:nat). variant n s /\ (n == 0 ==> s._3 == Ok)

noeq
[@@erasable]
type isl_triple : (pre : cond) -> (p : stmt) -> (post : cond) -> Type =
  | ISL_Assign : #pre : cond -> x : var -> e : expr ->
    isl_triple (is_ok pre) (Assign x e) 
      (is_ok (fun s -> exists x_init. 
        pre (x_init, s._2, s._3) /\ (s._1 x == Nat (eval_expr (x_init, s._2, s._3) e) /\
        (forall y. (y <> x) ==> s._1 y == x_init y))))
  
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
      isl_triple (is_ok (variant n)) p (variant (n + 1))) ->
    isl_triple (kleene_pre variant) (Kleene p) (kleene_post variant)

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
    isl_triple (is_ok pre)
      (Alloc x)
      (is_ok (fun s -> exists l v.
        s._1 x == Loc l /\
        l =!= 0 /\
        points_to l v s /\
        (exists x_old. pre (override s._1 x x_old, override s._2 l Unknown, Ok))))

  | ISL_Alloc2 : #pre : cond -> x : var -> l : loc ->
    isl_triple 
      (is_ok (fun s -> pre s /\ points_to_empty l s))
      (Alloc x)
      (is_ok (fun s -> exists (v x_old : value).
        s._1 x == Loc l /\
        l =!= 0 /\
        points_to l v s /\
        pre (override s._1 x x_old, override s._2 l Empty, Ok)))
  
  | ISL_Free : #pre : cond -> e : expr ->
    isl_triple
      (is_ok pre)
      (Free e)
      (is_ok (fun s -> exists (v : value).
        points_to_empty (eval_expr s e) s /\
        pre (s._1, override s._2 (eval_expr s e) (Full v), s._3)))

  | ISL_FreeEr : #pre : cond -> e : expr ->
    isl_triple
      (is_ok pre)
      (Free e)
      (fun s ->
        s._3 == Er /\
        points_to_empty (eval_expr s e) s /\
        pre (s._1, s._2, Ok))

  | ISL_FreeNull : #pre : cond -> e : expr ->
    isl_triple
      (is_ok pre)
      (Free e)
      (fun s -> s._3 == Er /\ eval_expr s e == 0 /\ pre (s._1, s._2, Ok))
  
  | ISL_Load : #pre : cond -> x : var -> e : expr ->
    isl_triple
      (is_ok pre)
      (Load x e)
      (is_ok (fun s -> exists l v x_old.
        eval_expr (override s._1 x x_old, s._2, Ok) e == l /\
        points_to l v s /\
        s._1 x == v /\
        pre (override s._1 x x_old, s._2, Ok)))

  | ISL_LoadEr : #pre : cond -> x : var -> e : expr ->
    isl_triple
      (is_ok pre)
      (Load x e)
      (fun s ->
        s._3 == Er /\
        points_to_empty (eval_expr s e) s /\
        pre (s._1, s._2, Ok))

  | ISL_LoadNull : #pre : cond -> x : var -> e : expr ->
    isl_triple
      (is_ok pre)
      (Load x e)
      (fun s -> s._3 == Er /\ eval_expr s e == 0 /\ pre (s._1, s._2, Ok))
  
  | ISL_Store : #pre : cond -> e1 : expr -> e2 : expr ->
    isl_triple
      (is_ok pre)
      (Store e1 e2)
      (is_ok (fun s ->
        points_to (eval_expr s e1) (Nat (eval_expr s e2)) s /\
        (exists v_old. pre (s._1, override s._2 (eval_expr s e1) (Full v_old), Ok))))

  | ISL_StoreEr : #pre : cond -> e1 : expr -> e2 : expr ->
    isl_triple
      (is_ok pre)
      (Store e1 e2)
      (fun s -> 
        s._3 == Er /\ 
        points_to_empty (eval_expr s e1) s /\
        pre (s._1, s._2, Ok))

  | ISL_StoreNull : #pre : cond -> e1 : expr -> e2 : expr ->
    isl_triple
      (is_ok pre)
      (Store e1 e2)
      (fun s -> 
        s._3 == Er /\ 
        eval_expr s e1 == 0 /\
        pre (s._1, s._2, Ok))

// ============================================================
// 6. Soundness of ISL
// ============================================================

let lemma_exists_tuple (#a #b : Type) (p : a -> b -> prop) :
  Lemma (requires (exists (x : a) (y : b). p x y))
        (ensures (exists (tup : a & b). p (fst tup) (snd tup))) = 
  let x = FStar.IndefiniteDescription.indefinite_description_ghost 
    a (fun x -> exists y. p x y) in
  let y = FStar.IndefiniteDescription.indefinite_description_ghost 
    b (fun y -> p x y) in
  let tup : a & b = (x, y) in
  assert (p (fst tup) (snd tup))

let rec soundness
  (p : stmt) (pre : cond) (post : cond)
  (pf : isl_triple pre p post)
  (s1 : state { post s1 })
  : GTot (s0 : state { pre s0 } & runsto p s0 s1) (decreases pf) 
  = match pf with
  | ISL_Assign #pre #x #e ->
    let (st1, hp1, m) = s1 in
    assert (p == Assign x e);
    assert (exists (st_init : store). pre (st_init, hp1, m) /\ 
            st1 x == Nat (eval_expr (st_init, hp1, m) e) /\
            (forall y. y <> x ==> st1 y == st_init y));
    let st_init = FStar.IndefiniteDescription.indefinite_description_ghost 
                  store (fun st_i -> pre (st_i, hp1, m) 
                  /\ st1 x == Nat (eval_expr (st_i, hp1, m) e)
                  /\ (forall y. y <> x ==> st1 y == st_i y))
    in
    let s0 = (st_init, hp1, Ok) in
    assert (pre s0);
    let pf0 = R_Assign x e s0 in
    assert (forall y. override st_init x (Nat (eval_expr s0 e)) y == s1._1 y);
    let pf1 : runsto (Assign x e) s0 s1 = R_Ext pf0 s0 s1 () () in
    (|s0, pf1|)
  
  | ISL_Nondet #pre #x -> 
    let (st1, hp1, m) = s1 in
    assert (p == Nondet x);
    assert (exists v. pre (override st1 x v, hp1, m));
    let v = FStar.IndefiniteDescription.indefinite_description_ghost
              _ (fun v -> pre (override st1 x v, hp1, m)) in
    assert (pre (override st1 x v, hp1, m));
    let s0 = (override st1 x v, hp1, Ok) in
    assert (pre s0);
    let pf0 = R_Nondet s0 #x (st1 x) in
    let pf1 : runsto (Nondet x) s0 s1 =
      R_Ext pf0 s0 s1 () ()
    in
    (|s0, pf1|)

  | ISL_Frame #p_pre #p_cmd #p_post fr pf_p _ ->
    let (st1, hp1, m) = s1 in
    let unfold p_two (h1 : heap) (h2 : heap) : prop = 
      heaps_disjoint h1 h2 /\ 
      hp1 == heap_union h1 h2 /\ 
      p_post (st1, h1, m) /\ 
      fr (st1, h2, m)
    in
    lemma_exists_tuple p_two;
    let logic_parts (hp_tup : heap & heap) : prop = 
      p_two (fst hp_tup) (snd hp_tup) 
    in
    let h_parts = FStar.IndefiniteDescription.indefinite_description_ghost (heap & heap) logic_parts in
    let h_ok = fst h_parts in
    let h_fr = snd h_parts in
    let (|s0_local, r_local|) = 
      soundness p_cmd (is_ok p_pre) p_post pf_p (st1, h_ok, m) in
    let (st0, hp0, m0) = s0_local in
    lemma_runsto_disjoint h_fr r_local;
    let s0 : state = (st0, heap_union hp0 h_fr, m0) in
    let r_global = r_frame r_local h_fr #() #() in
    lemma_runsto_modifies r_local;
    assert (match_except_vars (modifies p_cmd) st0 st1);
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
    assert (pre s1 /\ eval_expr s1 e =!= 0);
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
    else (
      let (|s0, r_p|) =
        soundness p (is_ok pre) mid pf_p s1 in
      let r = R_SeqEr #p #q #s0 #s1 r_p in
      (|s0, r|)
    )

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
    let p_n (n : nat) : prop = variant n s1 /\ (n == 0 ==> s1._3 == Ok) in
    assert (exists n. p_n n);
    let n = FStar.IndefiniteDescription.indefinite_description_ghost
            _ p_n in
    let rec aux (m : nat) (t : state { variant m t /\ (m == 0 ==> t._3 == Ok) })
      : GTot (s0 : state { variant 0 s0 /\ s0._3 == Ok } & runsto (Kleene p) s0 t) (decreases m) =
      if m = 0 then
        let s0 = t in
        let r = R_Kleene0 in
        (|s0, r|)
      else
        let m' = m - 1 in
        let pf_p = pf_var m' in
        let (|s_mid, r_p|) = 
          soundness p (is_ok (variant m')) (variant (m' + 1)) pf_p t in
        let (|s0, r_kleene|) = aux m' s_mid in
        let s_mid_ok : state = (s_mid._1, s_mid._2, Ok) in
        let r_kl_ok = R_Ext r_kleene s0 s_mid () () in
        let r_p_ok = R_Ext r_p s_mid t () () in
        let r_seq = 
          R_Seq #(Kleene p) #p #s0 #s_mid_ok #t r_kl_ok r_p_ok in
        let r = R_KleeneS #p #s0 #t r_seq in
        (|s0, r|)
    in
    aux n s1
  
  | ISL_Consequence #pre #p #post pre' post' pf_p _ _ ->
    let (|s0, r|) = soundness p (is_ok pre) post pf_p s1 in
    (|s0, r|)

  | ISL_Disjunction #pre1 #pre2 #p #post1 #post2 pf_p1 pf_p2 ->
    if t2b (post1 s1) then
      let (|s0, r|) = soundness p (is_ok pre1) post1 pf_p1 s1 in
      (|s0, r|)
    else (
      assert (post2 s1);
      let (|s0, r|) = soundness p (is_ok pre2) post2 pf_p2 s1 in
      (|s0, r|)
    )

  | ISL_Alloc1 #pre #x -> 
    let (st1, hp1, m1) = s1 in
    let unfold p_lv (l_i : loc) (v_i : value) : prop =
      st1 x == Loc l_i /\ l_i =!= 0 /\ points_to l_i v_i s1
    in
    lemma_exists_tuple p_lv;
    let logic_parts (lv : loc & value) : prop =
      p_lv (fst lv) (snd lv)
    in
    let lv_w = FStar.IndefiniteDescription.indefinite_description_ghost (loc & value) logic_parts in
    let l = fst lv_w in
    let v = snd lv_w in
    let p_xold (x_o : value) : prop =
      pre (override st1 x x_o, override hp1 l Unknown, Ok)
    in
    let x_old = FStar.IndefiniteDescription.indefinite_description_ghost value p_xold in
    let st0 = override st1 x x_old in
    let hp0 = override hp1 l Unknown in
    let s0 : state = (st0, hp0, Ok) in
    let r_alloc = R_Alloc s0 #x l v #() in
    let r = R_Ext r_alloc s0 s1 () () in
    assert pre s0;
    (|s0, r|)

  | ISL_Alloc2 #pre #x _ ->
    let (st1, hp1, m1) = s1 in
    let unfold p_lv (l_i : loc) (v_i : value) : prop =
      st1 x == Loc l_i /\ l_i =!= 0 /\ points_to l_i v_i s1
    in
    lemma_exists_tuple p_lv;
    let logic_parts (lv : loc & value) : prop =
      p_lv (fst lv) (snd lv)
    in
    let lv_w = FStar.IndefiniteDescription.indefinite_description_ghost (loc & value) logic_parts in
    let l = fst lv_w in
    let v = snd lv_w in
    let p_xold (x_o : value) : prop =
      pre (override st1 x x_o, override hp1 l Empty, Ok)
    in
    let x_old = FStar.IndefiniteDescription.indefinite_description_ghost value p_xold in
    let st0 = override st1 x x_old in
    let hp0 = override hp1 l Empty in
    let s0 : state = (st0, hp0, Ok) in
    let r_alloc = R_Alloc s0 #x l v in
    let r = R_Ext r_alloc s0 s1 () () in
    (|s0, r|)

  | ISL_Free #pre e -> 
    let (st1, hp1, m1) = s1 in
    let l = eval_expr s1 e in
    let p_v (v_i : value) : prop = 
      m1 == Ok /\ points_to_empty l s1 /\ pre (st1, override hp1 l (Full v_i), Ok) 
    in
    let v = FStar.IndefiniteDescription.indefinite_description_ghost value p_v in
    let st0 = st1 in
    let hp0 = override hp1 l (Full v) in
    let s0 : state = (st0, hp0, Ok) in
    let r_free = R_Free s0 e l v in
    let r = R_Ext r_free s0 s1 () () in
    (|s0, r|)

  | ISL_FreeEr #pre #e ->
    let (st, hp, m1) = s1 in
    let s0 = (st, hp, Ok) in
    let l = eval_expr s0 e in
    let r = R_FreeEr s0 e l in
    (|s0, r|)

  | ISL_FreeNull #pre #e ->
    let (st, hp, m1) = s1 in
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
    let x_old = FStar.IndefiniteDescription.indefinite_description_ghost value p_xold in
    let unfold p_lv (l_i : loc) (v_i : value) : prop =
      eval_expr (override st1 x x_old, hp1, Ok) e == l_i /\ 
      points_to l_i v_i s1 /\ st1 x == v_i /\
      pre (override st1 x x_old, hp1, Ok)
    in
    lemma_exists_tuple p_lv;
    let logic_parts (lv : loc & value) : prop = p_lv (fst lv) (snd lv) in
    let lv_w = FStar.IndefiniteDescription.indefinite_description_ghost (loc & value) logic_parts in
    let l = fst lv_w in
    let v = snd lv_w in
    let st0 = override st1 x x_old in
    let hp0 = hp1 in
    let s0 : state = (st0, hp0, Ok) in
    Classical.exists_intro (fun v_i -> points_to l v_i s0) v;
    let r_load = R_Load s0 x e l v in
    let st1' = override st0 x v in
    let r = R_Ext r_load s0 s1 () () in
    (|s0, r|)

  | ISL_LoadEr #pre #x #e ->
    let (st, hp, m1) = s1 in
    let s0 = (st, hp, Ok) in
    let l = eval_expr s0 e in
    let r = R_LoadEr s0 x e l in
    (|s0, r|)

  | ISL_LoadNull #pre #x #e ->
    let (st, hp, m1) = s1 in
    let s0 = (st, hp, Ok) in
    let r = R_LoadNull s0 x e in
    (|s0, r|)

  | ISL_Store #pre #e1 #e2 -> 
    let (st1, hp1, m1) = s1 in
    let p_l (l_i : loc) : prop =
      eval_expr s1 e1 == l_i /\ points_to l_i (Nat (eval_expr s1 e2)) s1
    in
    let l = FStar.IndefiniteDescription.indefinite_description_ghost loc p_l in
    let p_vold (v_o : value) : prop =
      pre (st1, override hp1 l (Full v_o), Ok)
    in
    let v_old = FStar.IndefiniteDescription.indefinite_description_ghost value p_vold in
    let st0 = st1 in
    let hp0 = override hp1 l (Full v_old) in
    let s0 = (st0, hp0, Ok) in
    Classical.exists_intro (fun v_i -> eval_expr s0 e1 == l /\ points_to l v_i s0) v_old;
    Classical.exists_intro (fun l_i -> exists v_i. eval_expr s0 e1 == l_i /\ points_to l_i v_i s0) l;
    let r_store = R_Store s0 e1 e2 l v_old in
    let hp1' = override hp0 l (Full (Nat (eval_expr s0 e2))) in
    let r = R_Ext r_store s0 s1 () () in
    (|s0, r|)

  | ISL_StoreEr #pre e1 e2 ->
    let (st, hp, m1) = s1 in
    let s0 = (st, hp, Ok) in
    let l = eval_expr s0 e1 in
    let r = R_StoreEr s0 e1 e2 l in
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
    (override st x (Nat (eval_expr (st, empty_heap, Ok) e)), empty_heap, Ok)
  
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
    h_p : heap { heaps_disjoint h_common h_p } -> 
    h_q : heap { heaps_disjoint h_common h_q /\ heaps_disjoint h_p h_q } -> 
    h0 : heap { heaps_disjoint h0 h_q } -> h1 : heap { heaps_disjoint h1 h_p } -> 
    m1 : term_mode ->
    footprint p (st0, h0, Ok) (stm, heap_union h_common h_p, Ok) ->
    footprint q (stm, heap_union h_common h_q, Ok) (st1, h1, m1) ->
    footprint (Seq p q) (st0, heap_union h0 h_q, Ok) (st1, heap_union h1 h_p, m1)
  
  | F_SeqEr : p : stmt -> q : stmt -> 
    s : state { s._3 == Ok } -> t : state { t._3 == Er } ->
    footprint p s t ->
    footprint (Seq p q) s t
  
  | F_ChoiceL : p : stmt -> q : stmt -> s : state { s._3 == Ok } -> t : state ->
    footprint p s t ->
    footprint (Choice p q) s t
  
  | F_ChoiceR : p : stmt -> q : stmt -> s : state { s._3 == Ok } -> t : state ->
    footprint q s t ->
    footprint (Choice p q) s t
  
  | F_Kleene0 : st : store -> p : stmt ->
    footprint (Kleene p) (st, empty_heap, Ok) (st, empty_heap, Ok)
  
  | F_KleeneS : p : stmt -> s : state { s._3 == Ok } -> t : state ->
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
    (st, singleton_full_heap l (Nat (eval_expr' st e2)), Ok)
  
  | F_StoreEr : st : store -> e1 : expr -> e2 : expr -> l : loc { l =!= 0 } ->
    #(squash (eval_expr' st e1 == l)) ->
    footprint (Store e1 e2) (st, singleton_empty_heap l, Ok)
    (st, singleton_empty_heap l, Er)
  
  | F_StoreNull : st : store -> e1 : expr -> e2 : expr ->
    #(squash (eval_expr' st e1 == 0)) ->
    footprint (Store e1 e2) (st, empty_heap, Ok) (st, empty_heap, Er)
  
  | F_StateEq : p : stmt -> s0 : state -> s1 : state -> footprint p s0 s1 ->
    s0' : state -> s1' : state -> 
    squash (state_equiv s0 s0') ->
    squash (state_equiv s1 s1') ->
    footprint p s0' s1'

// ============================================================
// 8. Soundness of footprints
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
      footprint_sound p (st0, h0, Ok) (stm, heap_union h_common h_p, Ok) f_p
    in
    let r_q =
      footprint_sound q (stm, heap_union h_common h_q, Ok) (st1, h1, m1) f_q
    in

    let r_p_framed = r_frame r_p h_q #() #() in
    let r_q_framed = r_frame r_q h_p #() #() in
    let s_mid_p = (stm, heap_union (heap_union h_common h_p) h_q, Ok) in
    let s_mid_q = (stm, heap_union (heap_union h_common h_q) h_p, Ok) in
    let s_final = (st1, heap_union h1 h_p, m1) in

    let r_q_aligned = R_Ext r_q_framed s_mid_p s_final () () in
    R_Seq #p #q #(st0, heap_union h0 h_q, Ok) #s_mid_p #s_final r_p_framed r_q_aligned
  
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
    R_Ext r s0 s1 () ()

  | F_AllocReuse st x l v ->
    let s0 = (st, singleton_empty_heap l, Ok) in
    let s1 = (override st x (Loc l), singleton_full_heap l v, Ok) in
    let r = R_Alloc s0 #x l v in
    R_Ext r s0 s1 () ()

  | F_Free st e l v ->
    let s0 = (st, singleton_full_heap l v, Ok) in
    let s1 = (st, override (singleton_full_heap l v) l Empty, Ok) in
    let r = R_Free s0 e l v in
    R_Ext r s0 (st, singleton_empty_heap l, Ok) () ()

  | F_FreeEr st e l ->
    R_FreeEr (st, singleton_empty_heap l, Ok) e l

  | F_FreeNull st e ->
    R_FreeNull (st, empty_heap, Ok) e

  | F_Load st x e l v -> 
    R_Load (st, singleton_full_heap l v, Ok) x e l v

  | F_LoadEr st x e l ->
    R_LoadEr (st, singleton_empty_heap l, Ok) x e l

  | F_LoadNull st x e ->
    R_LoadNull (st, empty_heap, Ok) x e

  | F_Store st e1 e2 l v ->
    let s0 = (st, singleton_full_heap l v, Ok) in
    let s1 = (st, override (singleton_full_heap l v) l (Full (Nat (eval_expr' st e2))), Ok) in
    let r = R_Store s0 e1 e2 l v in
    R_Ext r s0 (st, singleton_full_heap l (Nat (eval_expr' st e2)), Ok) () ()

  | F_StoreEr st e1 e2 l ->
    R_StoreEr (st, singleton_empty_heap l, Ok) e1 e2 l

  | F_StoreNull st e1 e2 ->
    R_StoreNull (st, empty_heap, Ok) e1 e2
  
  | F_StateEq p s0 s1 fp s0' s1' e0 e1 ->
    let r = footprint_sound p s0 s1 fp in
    R_Ext r s0' s1' e0 e1

// ============================================================
// 9. Frame closure of footprints
// ============================================================

noeq
type framed_footprint : stmt -> state -> state -> Type0 =
  | F_Frame : p : stmt -> s0 : state -> s1 : state -> h_fr : heap ->
    fp : footprint p s0 s1 -> 
    d0 : squash (heaps_disjoint s0._2 h_fr) ->
    d1 : squash (heaps_disjoint s1._2 h_fr) ->
    framed_footprint p (s0._1, heap_union s0._2 h_fr, s0._3) (s1._1, heap_union s1._2 h_fr, s1._3)
  
  | F_Ext : p : stmt -> s0 : state -> s1 : state ->
    framed_footprint p s0 s1 ->
    s0' : state -> s1' : state ->
    squash (state_equiv s0 s0') -> squash (state_equiv s1 s1') ->
    framed_footprint p s0' s1'

let rec framed_footprint_sound (p : stmt) (s0 : state) (s1 : state) (ff : framed_footprint p s0 s1)
  : GTot (runsto p s0 s1) (decreases ff) =
  match ff with
  | F_Frame p s0 s1 h_fr f_p _ _ ->
    let r_p = footprint_sound p s0 s1 f_p in
    r_frame r_p h_fr #() #()
  
  | F_Ext p s0 s1 f_p s0' s1' _ _ ->
    let r_p = framed_footprint_sound p s0 s1 f_p in
    R_Ext r_p s0' s1' _ _

// ============================================================
// 10. Cross-split and decomposition helpers
// ============================================================

let state_equiv_preserves_mode (s1 s2 : state) (#_ : squash (state_equiv s1 s2))
  : Lemma (ensures s1._3 == s2._3) = ()

let rec footprint_starts_ok (#p : stmt) (#s0 #s1 : state) (fp : footprint p s0 s1)
  : Lemma (ensures s0._3 == Ok) (decreases fp) =
  match fp with
  | F_StateEq _ s0 _ fp s0' _ e0 _ ->
    footprint_starts_ok fp;
    state_equiv_preserves_mode s0 s0' #e0
  | _ -> ()

let cell_merge (c1 c2 : cell) : cell =
  match c1 with
  | Unknown -> c2
  | _ -> c1

let heap_merge (h1 h2 : heap) : heap =
  fun l -> cell_merge (h1 l) (h2 l)

let cell_meet (c1 c2 : cell) : cell =
  match c1, c2 with
  | Unknown, _ -> Unknown
  | _, Unknown -> Unknown
  | _, _ -> c1

let cross_heap (h1 h2 : heap) : heap =
  fun l -> cell_meet (h1 l) (h2 l)

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
  heaps_disjoint h13 h14 /\
  heaps_disjoint h13 h23 /\
  heaps_disjoint h13 h24 /\
  heaps_disjoint h14 h23 /\
  heaps_disjoint h14 h24 /\
  heaps_disjoint h23 h24

noeq
type cross_split_witness (h1 h2 h3 h4 : heap) =
  | CrossSplit : h13 : heap -> h14 : heap -> h23 : heap -> h24 : heap ->
    squash (heaps_pairwise_disjoint h13 h14 h23 h24) ->
    squash (forall l. heap_merge h13 h14 l == h1 l) ->
    squash (forall l. heap_merge h23 h24 l == h2 l) ->
    squash (forall l. heap_merge h13 h23 l == h3 l) ->
    squash (forall l. heap_merge h14 h24 l == h4 l) ->
    cross_split_witness h1 h2 h3 h4

let heap_cross_split (h1 h2 h3 h4 : heap)
  (#_ : squash (heaps_disjoint h1 h2)) (#_ : squash (heaps_disjoint h3 h4))
  (#_ : squash (
    forall l.
      heap_merge h1 h2 l ==
      heap_merge h3 h4 l
  ))
  : GTot (cross_split_witness h1 h2 h3 h4) =
  let h13 = cross_heap h1 h3 in
  let h14 = cross_heap h1 h4 in
  let h23 = cross_heap h2 h3 in
  let h24 = cross_heap h2 h4 in

  let pointwise (l : loc)
    : Lemma (ensures (
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
  CrossSplit h13 h14 h23 h24 () () () () ()

noeq
type frame_parts (p : stmt) (s0 : state) (s1 : state) =
  | Parts : sl0 : state -> sl1 : state -> h_fr : heap -> fp : footprint p sl0 sl1 ->
    d0 : squash (heaps_disjoint sl0._2 h_fr) ->
    d1 : squash (heaps_disjoint sl1._2 h_fr) ->
    e0 : squash (state_equiv (sl0._1, heap_union sl0._2 h_fr, sl0._3) s0) ->
    e1 : squash (state_equiv (sl1._1, heap_union sl1._2 h_fr, sl1._3) s1) ->
    frame_parts p s0 s1

let rec flatten_framed (#p : stmt) (#s0 #s1 : state) (ff : framed_footprint p s0 s1)
  : GTot (frame_parts p s0 s1) (decreases ff) =
  match ff with
  | F_Frame _ sl0 sl1 h_fr fp d0 d1 ->
    Parts sl0 sl1 h_fr fp d0 d1 () ()

  | F_Ext _ sb0 sb1 ff_base s0' s1' e0 e1 ->
    match flatten_framed ff_base with
    | Parts sl0 sl1 h_fr fp d0 d1 e0' e1' ->
      let sf0 = (sl0._1, heap_union sl0._2 h_fr, sl0._3) in
      let sf1 = (sl1._1, heap_union sl1._2 h_fr, sl1._3) in
      Parts sl0 sl1 h_fr fp d0 d1 () ()

let rec map_framed_footprint (#p #q : stmt) (#s0 #s1 : state)
  (transform : (#sl0 : state -> #sl1 : state -> footprint p sl0 sl1 -> GTot (footprint q sl0 sl1)))
  (ff : framed_footprint p s0 s1)
  : GTot (framed_footprint q s0 s1) (decreases ff) =
  match ff with
  | F_Frame _ s0_local s1_local h_fr fp d0 d1 ->
    let fp' = transform fp in
    F_Frame q s0_local s1_local h_fr fp' d0 d1

  | F_Ext _ s0_base s1_base ff_base s0' s1' e0 e1 ->
    let ff_base' = map_framed_footprint transform ff_base in
    F_Ext q s0_base s1_base ff_base' s0' s1' e0 e1

let rec framed_seq_er (#p #q : stmt) (#s0 : state) (#s1 : state { s1._3 == Er })
  (ff  : framed_footprint p s0 s1)
  : GTot (framed_footprint (Seq p q) s0 s1) (decreases ff) =
  match ff with
  | F_Frame _ s0_local s1_local h_fr fp_p d0 d1 ->
    footprint_starts_ok fp_p;
    let fp_seq = F_SeqEr p q s0_local s1_local fp_p in
    F_Frame (Seq p q) s0_local s1_local h_fr fp_seq d0 d1

  | F_Ext _ s0_base s1_base ff_base s0' s1' e0 e1 ->
    state_equiv_preserves_mode s1_base s1' #e1;
    let ff_seq_base = framed_seq_er #p #q #s0_base #s1_base ff_base in
    F_Ext (Seq p q) s0_base s1_base ff_seq_base s0' s1' e0 e1

// ============================================================
// 11. Completeness of footprint decomposition
// ============================================================

let rec runsto_decompose (#p : stmt) (#s0 #s1 : state) (r : runsto p s0 s1)
  : GTot (framed_footprint p s0 s1) (decreases r) =
  match r with
  | R_Ext #p #s0 #s1 r_base s0' s1' eq0 eq1 -> 
    let ff = runsto_decompose r_base in
    F_Ext p s0 s1 ff s0' s1' eq0 eq1
  
  | R_Skip s ->
    let st = s._1 in
    let h = s._2 in
    let s_local = (st, empty_heap, Ok) in
    let s_framed = (st, heap_union empty_heap h, Ok) in
    let ff = F_Frame Skip s_local s_local h (F_Skip st) () () in
    F_Ext Skip s_framed s_framed ff s s () ()

  | R_Error s ->
    let st = s._1 in
    let h = s._2 in
    let s0_local = (st, empty_heap, Ok) in
    let s1_local = (st, empty_heap, Er) in
    let s0_framed = (st, heap_union empty_heap h, Ok) in
    let s1_framed = (st, heap_union empty_heap h, Er) in
    let ff = F_Frame Error s0_local s1_local h (F_Error st) () () in
    F_Ext Error s0_framed s1_framed ff s (st, h, Er) () ()
  
  | R_Assign x e s ->
    let st = s._1 in
    let h = s._2 in
    let s0_local = (st, empty_heap, Ok) in
    let st1 = override st x (Nat (eval_expr' st e)) in
    let s1_local = (st1, empty_heap, Ok) in
    let s0_framed = (st, heap_union empty_heap h, Ok) in
    let s1_framed = (st1, heap_union empty_heap h, Ok) in
    let ff = F_Frame (Assign x e) s0_local s1_local h (F_Assign st x e) () () in
    F_Ext (Assign x e) s0_framed s1_framed ff s (st1, h, Ok) () ()
  
  | R_Nondet s #x v ->
    let st = s._1 in
    let h = s._2 in
    let s0_local = (st, empty_heap, Ok) in
    let st1 = override st x v in
    let s1_local = (st1, empty_heap, Ok) in
    let s0_framed = (st, heap_union empty_heap h, Ok) in
    let s1_framed = (st1, heap_union empty_heap h, Ok) in
    let ff = F_Frame (Nondet x) s0_local s1_local h (F_Nondet st x v) () () in
    F_Ext (Nondet x) s0_framed s1_framed ff s (st1, h, Ok) () ()
  
  | R_Assume s #e _ ->
    let st = s._1 in
    let h = s._2 in
    let s_local = (st, empty_heap, Ok) in
    let s_framed = (st, heap_union empty_heap h, Ok) in
    let ff = F_Frame (Assume e) s_local s_local h (F_Assume st e) () () in
    F_Ext (Assume e) s_framed s_framed ff s s () ()
  
  | R_SeqEr #p #q #s #t r_p ->
    let ff_p = runsto_decompose r_p in
    framed_seq_er #p #q #s #t ff_p
  
  | R_Seq #p #q #s #t #u r_p r_q ->
    let ff_p = runsto_decompose r_p in
    let ff_q = runsto_decompose r_q in
    let parts_p = flatten_framed ff_p in
    let parts_q = flatten_framed ff_q in

    (match parts_p, parts_q with
    | Parts p0 p1 fr_p fp_p dp0 dp1 ep0 ep1,
      Parts q0 q1 fr_q fp_q dq0 dq1 eq0 eq1 ->
      let p_mid = (p1._1, heap_union p1._2 fr_p, p1._3) in
      let q_mid = (q0._1, heap_union q0._2 fr_q, q0._3) in
      let cs = heap_cross_split p1._2 fr_p q0._2 fr_q #dp1 #dq0 #() in

        (match cs with
        | CrossSplit h_common h_p h_q h_ext pairwise split_p split_fr_p 
          split_q split_fr_q ->
          let st0 = p0._1 in
          let stm = p1._1 in
          let st1 = q1._1 in
          let h0 = p0._2 in
          let h1 = q1._2 in
          let m1 = q1._3 in
          let p0_aligned = (st0, h0, Ok) in
          let p1_aligned = (stm, heap_union h_common h_p, Ok) in
          let q0_aligned = (stm, heap_union h_common h_q, Ok) in
          let q1_aligned = (st1, h1, m1) in
          let fp_p_aligned = F_StateEq p p0 p1 fp_p p0_aligned p1_aligned () () in
          let fp_q_aligned = F_StateEq q q0 q1 fp_q q0_aligned q1_aligned () () in
          let seq0_local = (st0, heap_union h0 h_q, Ok) in
          let seq1_local = (st1, heap_union h1 h_p, m1) in
          let fp_seq = F_Seq p q st0 stm st1 h_common h_p h_q h0 h1 m1 fp_p_aligned fp_q_aligned in
          let seq0_framed = (st0, heap_union (heap_union h0 h_q) h_ext, Ok) in
          let seq1_framed = (st1, heap_union (heap_union h1 h_p) h_ext, m1) in
          let ff_seq = F_Frame (Seq p q) seq0_local seq1_local h_ext fp_seq () () in
          let p0_framed = (st0, heap_union h0 fr_p, Ok) in
          let q1_framed = (st1, heap_union h1 fr_q, m1) in
          F_Ext (Seq p q) seq0_framed seq1_framed ff_seq s u () ()))
  
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
  
  | R_Kleene0 #p #s ->
    let st = s._1 in
    let h = s._2 in
    let s_local = (st, empty_heap, Ok) in
    let s_framed = (st, heap_union empty_heap h, Ok) in
    let ff = F_Frame (Kleene p) s_local s_local h (F_Kleene0 st p) () () in
    F_Ext (Kleene p) s_framed s_framed ff s s () ()
  
  | R_KleeneS #p #s #t r_seq ->
    let ff_seq = runsto_decompose r_seq in
    map_framed_footprint (fun #sl0 #sl1 fp_seq ->
      footprint_starts_ok fp_seq;
      F_KleeneS p sl0 sl1 fp_seq) ff_seq
  
  | R_Alloc s #x l v ->
    let st = s._1 in
    let h = s._2 in
    let h_fr = heap_without h l in
    let st1 = override st x (Loc l) in

    if Unknown? (h l) then
      let s0_local = (st, empty_heap, Ok) in
      let s1_local = (st1, singleton_full_heap l v, Ok) in
      let s0_framed = (st, heap_union empty_heap h_fr, Ok) in
      let s1_framed = (st1, heap_union (singleton_full_heap l v) h_fr, Ok) in
      let fp_alloc = F_AllocFresh st x l v in
      let ff = F_Frame (Alloc x) s0_local s1_local h_fr fp_alloc () () in
      F_Ext (Alloc x) s0_framed s1_framed ff s0 s1 () ()
    else (
      let s0_local = (st, singleton_empty_heap l, Ok) in
      let s1_local = (st1, singleton_full_heap l v, Ok) in
      let s0_framed = (st, heap_union (singleton_empty_heap l) h_fr, Ok) in
      let s1_framed = (st1, heap_union (singleton_full_heap l v) h_fr, Ok) in
      let fp_alloc = F_AllocReuse st x l v in
      let ff = F_Frame (Alloc x) s0_local s1_local h_fr fp_alloc () () in
      F_Ext (Alloc x) s0_framed s1_framed ff s0 s1 () ()
    )
  
  | R_Free s e l v ->
    let st = s._1 in
    let h = s._2 in
    let h_fr = heap_without h l in
    let s0_local = (st, singleton_full_heap l v, Ok) in
    let s1_local = (st, singleton_empty_heap l, Ok) in
    let s0_framed = (st, heap_union (singleton_full_heap l v) h_fr, Ok) in
    let s1_framed = (st, heap_union (singleton_empty_heap l) h_fr, Ok) in
    let fp_free = F_Free st e l v in
    let ff = F_Frame (Free e) s0_local s1_local h_fr fp_free () () in
    F_Ext (Free e) s0_framed s1_framed ff s0 s1 () ()
  
  | R_FreeEr s e l ->
    let st = s._1 in
    let h = s._2 in
    let h_fr = heap_without h l in
    let s0_local = (st, singleton_empty_heap l, Ok) in
    let s1_local = (st, singleton_empty_heap l, Er) in
    let s0_framed = (st, heap_union (singleton_empty_heap l) h_fr, Ok) in
    let s1_framed = (st, heap_union (singleton_empty_heap l) h_fr, Er) in
    let f_free = F_FreeEr st e l #() in
    let ff = F_Frame (Free e) s0_local s1_local h_fr f_free () () in
    F_Ext (Free e) s0_framed s1_framed ff s0 s1 () ()
  
  | R_FreeNull s e ->
    let st = s._1 in
    let h = s._2 in
    let s0_local = (st, empty_heap, Ok) in
    let s1_local = (st, empty_heap, Er) in
    let s0_framed = (st, heap_union empty_heap h, Ok) in
    let s1_framed = (st, heap_union empty_heap h, Er) in
    let f_free = F_FreeNull st e #() in
    let ff = F_Frame (Free e) s0_local s1_local h f_free () () in
    F_Ext (Free e) s0_framed s1_framed ff s0 s1 () ()
  
  | R_Load s x e l v ->
    let st = s._1 in
    let h = s._2 in
    let h_fr = heap_without h l in
    let s0_local = (st, singleton_full_heap l v, Ok) in
    let st1 = override st x v in
    let s1_local = (st1, singleton_full_heap l v, Ok) in
    let s0_framed = (st, heap_union (singleton_full_heap l v) h_fr, Ok) in
    let s1_framed = (st1, heap_union (singleton_full_heap l v) h_fr, Ok) in
    let fp_load = F_Load st x e l v #() in
    let ff = F_Frame (Load x e) s0_local s1_local h_fr fp_load () () in
    F_Ext (Load x e) s0_framed s1_framed ff s0 s1 () ()
  
  | R_LoadEr s x e l ->
    let st = s._1 in
    let h = s._2 in
    let h_fr = heap_without h l in
    let s0_local = (st, singleton_empty_heap l, Ok) in
    let s1_local = (st, singleton_empty_heap l, Er) in
    let s0_framed = (st, heap_union (singleton_empty_heap l) h_fr, Ok) in
    let s1_framed = (st, heap_union (singleton_empty_heap l) h_fr, Er) in
    let f_load = F_LoadEr st x e l #() in
    let ff = F_Frame (Load x e) s0_local s1_local h_fr f_load () () in
    F_Ext (Load x e) s0_framed s1_framed ff s0 s1 () ()
  
  | R_LoadNull s x e ->
    let st = s._1 in
    let h = s._2 in
    let s0_local = (st, empty_heap, Ok) in
    let s1_local = (st, empty_heap, Er) in
    let s0_framed = (st, heap_union empty_heap h, Ok) in
    let s1_framed = (st, heap_union empty_heap h, Er) in
    let f_load = F_LoadNull st x e #() in
    let ff = F_Frame (Load x e) s0_local s1_local h f_load () () in
    F_Ext (Load x e) s0_framed s1_framed ff s0 s1 () ()
  
  | R_Store s e1 e2 l v ->
    let st = s._1 in
    let h = s._2 in
    let h_fr = heap_without h l in
    let s0_local = (st, singleton_full_heap l v, Ok) in
    let h1 = singleton_full_heap l (Nat (eval_expr' st e2)) in
    let s1_local = (st, h1, Ok) in
    let s0_framed = (st, heap_union (singleton_full_heap l v) h_fr, Ok) in
    let s1_framed = (st, heap_union h1 h_fr, Ok) in
    let fp_store = F_Store st e1 e2 l v in
    let ff = F_Frame (Store e1 e2) s0_local s1_local h_fr fp_store () () in
    F_Ext (Store e1 e2) s0_framed s1_framed ff s0 s1 () ()

  | R_StoreEr s e1 e2 l ->
    let st = s._1 in
    let h = s._2 in
    let h_fr = heap_without h l in
    let s0_local = (st, singleton_empty_heap l, Ok) in
    let s1_local = (st, singleton_empty_heap l, Er) in
    let s0_framed = (st, heap_union (singleton_empty_heap l) h_fr, Ok) in
    let s1_framed = (st, heap_union (singleton_empty_heap l) h_fr, Er) in
    let f_store = F_StoreEr st e1 e2 l #() in
    let ff = F_Frame (Store e1 e2) s0_local s1_local h_fr f_store () () in
    F_Ext (Store e1 e2) s0_framed s1_framed ff s0 s1 () ()
  
  | R_StoreNull s e1 e2 ->
    let st = s._1 in
    let h = s._2 in
    let s0_local = (st, empty_heap, Ok) in
    let s1_local = (st, empty_heap, Er) in
    let s0_framed = (st, heap_union empty_heap h, Ok) in
    let s1_framed = (st, heap_union empty_heap h, Er) in
    let f_store = F_StoreNull st e1 e2 #() in
    let ff = F_Frame (Store e1 e2) s0_local s1_local h f_store () () in
    F_Ext (Store e1 e2) s0_framed s1_framed ff s0 s1 () ()