module IncSepLogic

open FStar.Classical

module S = FStar.StrongExcludedMiddle
module FE = FStar.FunctionalExtensionality
open FStar.FunctionalExtensionality { (^->) }

unfold
let p2b (p : prop) : GTot bool = S.strong_excluded_middle p

let unreachable #a (_ : squash False) : a = coerce_eq () ()

type var = string
type loc = nat
type value = 
  | Nat of nat 
  | Loc of loc

type cell =
  | Full of value
  | Empty // Es mío, pero lo destruí - la celda SÍ pertenece a mi footprint y tengo la certeza de que fue liberada con Free
  | Unknown // No es mío - la celda NO pertenece a mi footprint

type store = var -> value
type heap = loc -> cell

let heap_is_complete (h : heap) : prop =
  forall l. ~ (Unknown? (h l))

let complete_heap : Type = h : heap{heap_is_complete h}

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
  | Local : var -> stmt -> stmt
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

type state = store & heap

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
    | Times e1 e2 -> Prims.op_Multiply (eval_expr' s e1) (eval_expr' s e2)
    | Eq e1 e2 -> if eval_expr' s e1 = eval_expr' s e2
                  then 0 else 1
    | Lt e1 e2 -> if eval_expr' s e1 < eval_expr' s e2
                  then 0 else 1
    | Gt e1 e2 -> if eval_expr' s e1 > eval_expr' s e2
                  then 0 else 1

let eval_expr (s : state) (e : expr) : GTot nat = eval_expr' (fst s) e

let override (#a : eqtype) (#b : Type) (f : a -> b) (x : a) (y : b) : a -> b =
  fun z -> if z = x then y else f z

// disjunción de celdas
let cell_disjoint (c1 c2 : cell) : prop =
  c1 == Unknown \/ c2 == Unknown

// unión de celdas
// GM: Agregué el refinamiento
let cell_union (c1 c2 : cell{cell_disjoint c1 c2}) : cell =
  match c1 with
    | Unknown -> c2
    | _ -> c1

// disjunción de heaps
let heaps_disjoint (h1 h2 : heap) : prop =
  forall l. cell_disjoint (h1 l) (h2 l)

// unión de heaps
// GM: Agregué el refinamiento
let heap_union (h1 h2 : heap{heaps_disjoint h1 h2}) : heap =
  fun l -> cell_union (h1 l) (h2 l)

// Semántica del lenguaje
noeq
type runsto : (p : stmt) -> (s0 : state) -> (m : term_mode) -> (s1 : state) -> Type0 =
  | R_Ext : #p:stmt -> #s0:state -> #m:term_mode -> #s1:state ->
    runsto p s0 m s1 -> s0' : state -> s1' : state ->
    (squash (forall (x:var). fst s0 x == fst s0' x)) -> 
    (squash (forall (l:loc). snd s0 l == snd s0' l)) -> 
    (squash (forall (x:var). fst s1 x == fst s1' x)) ->
    (squash (forall (l:loc). snd s1 l == snd s1' l)) ->
    runsto p s0' m s1'
  | R_Skip : s : state -> runsto Skip s Ok s
  | R_Error : s : state -> runsto Error s Er s
  | R_Assign : x : var -> 
    e : expr -> s : state -> 
    runsto (Assign x e) s Ok (let (st, hp) = s in
    override st x (Nat (eval_expr s e)), hp)
  | R_Nondet : s : state -> #x : var -> v : value ->
    runsto (Nondet x) s Ok (let (st, hp) = s in
    override st x v, hp)
  | R_Assume : s : state -> #e : expr -> 
    squash (eval_expr s e == 0) ->
    runsto (Assume e) s Ok s
  | R_SeqEr : #p : stmt -> #q : stmt ->
    #s : state -> #t : state ->
    runsto p s Er t -> runsto (Seq p q) s Er t
  | R_Seq : #p : stmt -> #q : stmt -> #m : term_mode ->
    #s : state -> #t : state -> #u : state ->
    runsto p s Ok t -> runsto q t m u ->
    runsto (Seq p q) s m u
  | R_ChoiceL : #p : stmt -> #q : stmt ->
    #s : state -> #m : term_mode -> #t : state ->
    runsto p s m t -> runsto (Choice p q) s m t
  | R_ChoiceR : #p : stmt -> #q : stmt ->
    #s: state -> #m : term_mode -> #t : state ->
    runsto q s m t -> runsto (Choice p q) s m t
  | R_Kleene0 : #p : stmt -> #s : state -> 
    runsto (Kleene p) s Ok s
  | R_KleeneS : #p : stmt -> #s : state ->
    #m : term_mode -> #t : state ->
    runsto (Seq (Kleene p) p) s m t ->
    runsto (Kleene p) s m t
  | R_Local : s : state -> #x : var -> #p : stmt -> 
    m : term_mode -> t : state -> v : value ->
    runsto p ((override (fst s) x v), (snd s)) m t ->
    runsto (Local x p) s m ((fun y -> if x = y then (fst s) y else (fst t) y), (snd t))

  // No hay comando Frame en los programas!
  // | R_Frame : #p : stmt -> #s0 : state -> #m : term_mode -> #s1 : state ->
  //   runsto p s0 m s1 -> h_fr : heap ->
  //   (squash (heaps_disjoint (snd s0) h_fr)) ->
  //   (squash (heaps_disjoint (snd s1) h_fr)) ->
  //   runsto p (fst s0, heap_union (snd s0) h_fr) m (fst s1, heap_union (snd s1) h_fr)
  // |[ L : x := alloc()]|ok = {(σ, (s[x |-> l], h[l |-> v])) | 
  // σ = (s, h) ∧ v ∈ Val /\ (l ∉ dom(h) \/ h(l) = ⊥)}
  | R_Alloc : s : state -> #x : var -> l : loc{l =!= 0} -> v : value ->
    #(squash (snd s l == Empty)) ->
    runsto (Alloc x) s Ok (let (st, hp) = s in
    override st x (Loc l), override hp l (Full v))
  // |[ L : free(x)]|ok = {(σ, (s, h[s(x) |-> ⊥])) | σ = (s, h) ∧ h(s(x)) ∈ Val}
  | R_Free : s : state -> e : expr -> l : loc ->
    #(squash (eval_expr s e == l /\ l =!= 0)) ->
    #(squash (Full? (snd s l))) ->
    runsto (Free e) s Ok (let (st, hp) = s in
    st, override hp l Empty)
    // |[L : free(x)]|er(L') = {(σ, σ) | L = L' /\ σ = (s, h) ∧ (s(x) = null \/ h(s(x)) = ⊥)}
  | R_FreeEr : s : state -> e : expr -> l : loc ->
    #(squash (eval_expr s e == l)) ->
    #(squash (l == 0 \/ snd s l == Empty)) ->
    runsto (Free e) s Er s
  | R_FreeNull : s : state -> e : expr ->
    #(squash (eval_expr s e == 0)) ->
    runsto (Free e) s Er s
  // |[L : x := [y]]|ok = {(σ, (s, h[x |-> v])) | σ = (s, h) ∧ h(s(y)) = v ∈ Val}
  | R_Load : s : state -> x : var -> e : expr ->
    l : loc -> v : value ->
    #(squash (snd s l == Full v)) ->
    #(squash (eval_expr s e == l)) ->
    runsto (Load x e) s Ok (let (st, hp) = s in
    override st x v, hp)
  // |[L : x := [y]]|er(L') = {(σ, σ) | L = L' /\ σ = (s, h) ∧ (s(x) = null \/ h(s(x)) = ⊥)}
  | R_LoadEr : s : state -> x : var -> 
    e : expr -> l : loc ->
    #(squash (eval_expr s e == l)) ->
    #(squash (l == 0 \/ snd s l == Empty)) ->
    runsto (Load x e) s Er s
  | R_LoadNull : s : state -> x : var -> e : expr ->
    #(squash (eval_expr s e == 0)) ->
    runsto (Load x e) s Er s
  // |[L : [x] := y]|ok = {(σ, (s, h[s(x) |-> s(y)])) | σ = (s, h) ∧ h(s(x)) ∈ Val}
  | R_Store : s : state -> e1 : expr -> e2 : expr ->
    l : loc -> v : value ->
    #(squash (snd s l == Full v)) ->
    #(squash (eval_expr s e1 == l)) ->
    runsto (Store e1 e2) s Ok (let (st, hp) = s in
    st, override hp l (Full (Nat (eval_expr s e2))))
  // |[L : [x] := y]|er(L') = {(σ, σ) | L = L' /\ σ = (s, h) ∧ (s(x) = null \/ h(s(x)) = ⊥)}
  | R_StoreEr : s : state -> e1 : expr ->
    e2 : expr -> l : loc ->
    #(squash (eval_expr s e1 == l)) ->
    #(squash (l == 0 \/ snd s l == Empty)) ->
    runsto (Store e1 e2) s Er s
  | R_StoreNull : s : state -> e1 : expr -> e2 : expr ->
    #(squash (eval_expr s e1 == 0)) ->
    runsto (Store e1 e2) s Er s

let rec lemma_runsto_disjoint (#p:stmt) (#s0:state) (#m:term_mode) (#s1:state) 
  (h_fr:heap) (r:runsto p s0 m s1) :
  Lemma (requires (heaps_disjoint (snd s1) h_fr))
        (ensures  (heaps_disjoint (snd s0) h_fr))
        (decreases r) 
  = match r with
  | R_Ext r' _ _ _ _ _ _ ->
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
  | R_Local _ _ _ _ r' ->
    lemma_runsto_disjoint h_fr r'
  // | R_Frame r' _ _ _ ->
  //   lemma_runsto_disjoint h_fr r'
  | _ -> ()

let rec r_frame (#p:stmt) (#s0 : state) (#m : term_mode) (#s1 : state)
  (r : runsto p s0 m s1) (h_fr : heap)
  (#_ : squash (heaps_disjoint (snd s0) h_fr))
  (#_ : squash (heaps_disjoint (snd s1) h_fr)) :
  GTot (runsto p (fst s0, heap_union (snd s0) h_fr) m (fst s1, heap_union (snd s1) h_fr))
  (decreases r) = 
  let s0_fr = (fst s0, heap_union (snd s0) h_fr) in
  let s1_fr = (fst s1, heap_union (snd s1) h_fr) in
  match r with
  | R_Ext r' _ _ _ _ _ _ ->
    let r_fr = r_frame r' h_fr #() #() in
    R_Ext r_fr s0_fr s1_fr () () () ()
  | R_Skip _ ->
    R_Ext (R_Skip s0_fr) s0_fr s1_fr () () () ()
  | R_Error _ ->
    R_Ext (R_Error s0_fr) s0_fr s1_fr () () () ()
  | R_Assign x e s ->
    R_Ext (R_Assign x e s0_fr) s0_fr s1_fr () () () ()
  | R_Nondet _ #x v ->
    R_Ext (R_Nondet s0_fr #x v) s0_fr s1_fr () () () ()
  | R_Assume _ #e _ ->
    R_Ext (R_Assume s0_fr #e ()) s0_fr s1_fr () () () ()
  | R_SeqEr #p #q r_p ->
    let r_p_fr = r_frame r_p h_fr #() #() in
    R_Ext (R_SeqEr #p #q r_p_fr) s0_fr s1_fr () () () ()
  | R_Seq r_p r_q ->
    lemma_runsto_disjoint h_fr r_q;
    let r_p_fr = r_frame r_p h_fr #() #() in
    let r_q_fr = r_frame r_q h_fr #() #() in
    R_Ext (R_Seq r_p_fr r_q_fr) s0_fr s1_fr () () () ()
  | R_ChoiceL #p #q r_p ->
    let r_p_fr = r_frame r_p h_fr #() #() in
    R_Ext (R_ChoiceL #p #q r_p_fr) s0_fr s1_fr () () () ()
  | R_ChoiceR #p #q r_q ->
    let r_q_fr = r_frame r_q h_fr #() #() in
    R_Ext (R_ChoiceR #p #q r_q_fr) s0_fr s1_fr () () () ()
  | R_Kleene0 #p ->
    R_Ext (R_Kleene0 #p #s0_fr) s0_fr s1_fr () () () ()
  | R_KleeneS r_seq ->
    let r_seq_fr = r_frame r_seq h_fr #() #() in
    R_Ext (R_KleeneS r_seq_fr) s0_fr s1_fr () () () ()
  | R_Local s #x #p m t v r_inner ->
    let r_inner_fr = r_frame r_inner h_fr #() #() in
    let t_fr = (fst t, heap_union (snd t) h_fr) in
    let r0 = R_Local s0_fr #x #p m t_fr v r_inner_fr in
    R_Ext r0 s0_fr s1_fr () () () ()
  | R_Alloc _ #x l v ->
    R_Ext (R_Alloc s0_fr #x l v) s0_fr s1_fr () () () ()
  | R_Free s e l ->
    R_Ext (R_Free s0_fr e l) s0_fr s1_fr () () () ()
  | R_FreeEr s e l ->
    R_Ext (R_FreeEr s0_fr e l) s0_fr s1_fr () () () ()
  | R_FreeNull s e ->
    R_Ext (R_FreeNull s0_fr e) s0_fr s1_fr () () () ()
  | R_Load s x e l v ->
    R_Ext (R_Load s0_fr x e l v) s0_fr s1_fr () () () ()
  | R_LoadEr s x e l ->
    R_Ext (R_LoadEr s0_fr x e l) s0_fr s1_fr () () () ()
  | R_LoadNull s x e ->
    R_Ext (R_LoadNull s0_fr x e) s0_fr s1_fr () () () ()
  | R_Store s e1 e2 l v ->
    R_Ext (R_Store s0_fr e1 e2 l v) s0_fr s1_fr () () () ()
  | R_StoreEr s e1 e2 l ->
    R_Ext (R_StoreEr s0_fr e1 e2 l) s0_fr s1_fr () () () ()
  | R_StoreNull s e1 e2 ->
    R_Ext (R_StoreNull s0_fr e1 e2) s0_fr s1_fr () () () ()

// definir operador * de logica de separacion
unfold
let sep_conj (p q : cond) : cond =
  fun (st, hp) -> 
    exists h1 h2.
      heaps_disjoint h1 h2 /\
      hp == heap_union h1 h2 /\
      p (st, h1) /\ q (st, h2)

unfold let ( ** ) = sep_conj

let emp : cond =
  fun (st, hp) ->
    forall l. hp l == Unknown \/ hp l == Empty

let points_to (l : loc) (v : value) : cond =
  fun (st, hp) -> 
  l =!=0 /\
  hp l == Full v /\
  forall l'. (l' <> l) ==> (hp l' == Unknown)

let points_to_empty (l : loc) : cond =
  fun (st, hp) -> 
    l =!= 0 /\
    hp l == Empty /\
    (forall l'. (l' <> l) ==> (hp l' == Unknown))

let test1 (l:loc) (v1 v2:value) (s:state) :
  Lemma (requires ( (points_to l v1 ** points_to l v2) s ))
        (ensures  ( False ))
= ()

(* Los stores st1 y st2 son idénticos excepto por las variables en vars. *)
let match_except_vars (vars : string -> prop) (st1 st2 : store) : prop =
  forall x. ~(vars x) ==> st1 x == st2 x

let independent_on_vars (vars : string -> prop) (c : cond) : prop =
  forall st1 st2 hp.
    match_except_vars vars st1 st2 ==> (c (st1, hp) <==> c (st2, hp))

let rec modifies (p : stmt) (x : var) : prop =
  match p with
  | Assign y _ -> x = y
  | Nondet y -> x = y
  | Local y s -> x <> y /\ modifies s x
  | Seq s1 s2 -> modifies s1 x \/ modifies s2 x
  | Choice s1 s2 -> modifies s1 x \/ modifies s2 x
  | Kleene s -> modifies s x
  | Alloc y -> x = y
  | Load y _ -> x = y
  | _ -> False

noeq
type isl_triple : (pre : cond) -> (p : stmt) -> (post_ok : cond) -> (post_er : cond) -> Type =
  | ISL_Assign : #pre : cond -> x : var -> e : expr ->
    isl_triple pre (Assign x e) 
      (fun (st, hp) -> exists x_init. 
        pre (x_init, hp) /\ (st x == Nat (eval_expr (x_init, hp) e) /\
        (forall y. (y <> x) ==> st y == x_init y))) (fun s -> false)
  
  | ISL_Nondet : #pre : cond -> x : var -> 
    isl_triple pre (Nondet x)
      (fun (st, hp) -> exists v.
        pre (override st x v, hp)) (fun s -> false)
  
  | ISL_Skip : #pre : cond ->
    isl_triple pre Skip pre (fun s -> false)
  
  | ISL_Error : #pre : cond ->
    isl_triple pre Error (fun s -> false) pre
  
  | ISL_Assume : #pre : cond -> e : expr ->
    isl_triple pre (Assume e)
      (fun s -> pre s /\ (eval_expr s e == 0)) (fun s -> false)
  
  | ISL_Seq : #p : stmt -> #q : stmt ->
    #pre : cond -> #mid_ok : cond -> #mid_er : cond ->
    #post_ok : cond -> #post_er : cond ->
    isl_triple pre p mid_ok mid_er ->
    isl_triple mid_ok q post_ok post_er ->
    isl_triple pre (Seq p q) post_ok (fun s -> mid_er s \/ post_er s)
  
  | ISL_ChoiceL : #p : stmt -> #q : stmt ->
    #pre : cond -> #post_ok : cond -> #post_er : cond ->
    isl_triple pre p post_ok post_er ->
    isl_triple pre (Choice p q) post_ok post_er
  
  | ISL_ChoiceR : #p : stmt -> #q : stmt ->
    #pre : cond -> #post_ok : cond -> #post_er : cond ->
    isl_triple pre q post_ok post_er ->
    isl_triple pre (Choice p q) post_ok post_er
  
  | ISL_Kleene0 : #p : stmt ->#pre : cond ->
    isl_triple pre (Kleene p) pre (fun s -> false)
  
  | ISL_KleeneS : #p : stmt -> #pre : cond ->
    #post_ok : cond -> #post_er : cond ->
    isl_triple pre (Seq (Kleene p) p) post_ok post_er ->
    isl_triple pre (Kleene p) post_ok post_er
  
  | ISL_KleeneVariant : #variant : (nat -> cond) ->
    #p : stmt -> step_proof : (n : nat ->
      GTot (isl_triple (variant n) p (variant (n + 1)) (fun s -> false))) ->
    isl_triple (variant 0) (Kleene p) (fun s -> exists n. variant n s) (fun _ -> false)
  
  | ISL_Empty : #p : stmt ->
    isl_triple (fun s -> false) p (fun s -> false) (fun s -> false)

  | ISL_Consequence : #pre : cond -> #p : stmt ->
    #post_ok : cond -> #post_er : cond ->
    pre' : cond -> post_ok' : cond -> post_er' : cond ->
    isl_triple pre p post_ok post_er ->
    squash (forall x. pre x ==> pre' x) ->
    squash (forall x. post_ok' x ==> post_ok x) ->
    squash (forall x. post_er' x ==> post_er x) ->
    isl_triple pre' p post_ok' post_er'

  | ISL_Disjunction : #pre1 : cond -> #pre2 : cond ->
    #p : stmt -> #post_ok1 : cond -> #post_ok2 : cond ->
    #post_er1 : cond -> #post_er2 : cond ->
    isl_triple pre1 p post_ok1 post_er1 ->
    isl_triple pre2 p post_ok2 post_er2 ->
    isl_triple (fun s -> pre1 s \/ pre2 s) p
      (fun s -> post_ok1 s \/ post_ok2 s)
      (fun s -> post_er1 s \/ post_er2 s)

  | ISL_Frame : #pre : cond -> #p : stmt ->
    #post_ok : cond -> #post_er : cond -> fr : cond ->
    isl_triple pre p post_ok post_er ->
    squash (independent_on_vars (modifies p) fr) ->
    isl_triple (pre ** fr) p
      (post_ok ** fr)
      (post_er ** fr)
  
  | ISL_Alloc1 : x : var ->
    isl_triple emp
      (Alloc x)
      (fun (st, hp) -> exists l v.
        st x == Loc l /\
        l =!= 0 /\
        points_to l v (st, hp)) 
      (fun s -> false)

  | ISL_Alloc2 : x : var -> l : loc ->
    isl_triple 
      (fun s0 -> points_to_empty l s0)
      (Alloc x)
      (fun (st, hp) -> exists v.
        st x == Loc l /\
        l =!= 0 /\
        points_to l v (st, hp)) 
      (fun s -> false)
  
  | ISL_Free : e : expr ->
    isl_triple
      (fun s -> exists v. points_to (eval_expr s e) v s)
      (Free e)
      (fun s -> points_to_empty (eval_expr s e) s)
      (fun s -> false)

  | ISL_FreeEr : e : expr ->
    isl_triple
      (fun s -> points_to_empty (eval_expr s e) s)
      (Free e)
      (fun s -> false)
      (fun s -> points_to_empty (eval_expr s e) s)

  | ISL_FreeNull : e : expr ->
    isl_triple
      (fun s -> eval_expr s e == 0)
      (Free e)
      (fun s -> false)
      (fun s -> eval_expr s e == 0)
  
  | ISL_Load : x : var -> e : expr ->
    isl_triple
      (fun s -> exists v. points_to (eval_expr s e) v s)
      (Load x e)
      (fun s -> exists v. 
        points_to (eval_expr s e) v s /\
        fst s x == v)
      (fun s -> false)

  | ISL_LoadEr : x : var -> e : expr ->
    isl_triple
      (fun s -> points_to_empty (eval_expr s e) s)
      (Load x e)
      (fun s -> false)
      (fun s -> points_to_empty (eval_expr s e) s)

  | ISL_LoadNull : x : var -> e : expr ->
    isl_triple
      (fun s -> eval_expr s e == 0)
      (Load x e)
      (fun s -> false)
      (fun s -> eval_expr s e == 0)
  
  | ISL_Store : e1 : expr -> e2 : expr ->
    isl_triple
      (fun s -> exists v. points_to (eval_expr s e1) v s)
      (Store e1 e2)
      (fun s -> points_to (eval_expr s e1) (Nat (eval_expr s e2)) s)
      (fun s -> false)
    
  | ISL_StoreEr : e1 : expr -> e2 : expr ->
    isl_triple
      (fun s -> points_to_empty (eval_expr s e1) s)
      (Store e1 e2)
      (fun s -> false)
      (fun s -> points_to_empty (eval_expr s e1) s)

  | ISL_StoreNull : e1 : expr -> e2 : expr ->
    isl_triple
      (fun s -> eval_expr s e1 == 0)
      (Store e1 e2)
      (fun s -> false)
      (fun s -> eval_expr s e1 == 0)

let lemma_exists_tuple (#a #b: Type) (p: a -> b -> prop) :
  Lemma (requires (exists (x:a) (y:b). p x y))
        (ensures (exists (tup: a & b). p (fst tup) (snd tup))) 
  = 
  let x = FStar.IndefiniteDescription.indefinite_description_ghost 
            a (fun x -> exists y. p x y) in
  let y = FStar.IndefiniteDescription.indefinite_description_ghost 
            b (fun y -> p x y) in
  let tup : a & b = (x, y) in
  assert (p (fst tup) (snd tup))

let lemma_runsto_modifies (#p : stmt) (#s0 #s1 : state) (#m : term_mode) (r: runsto p s0 m s1) 
  : Lemma (ensures match_except_vars (modifies p) (fst s0) (fst s1)) =
  admit()

let rec soundness_ok
  (p : stmt) (pre : cond) (post_ok : cond) (post_er : cond)
  (pf : isl_triple pre p post_ok post_er)
  (s1 : state { post_ok s1 })
  : GTot (s0 : state { pre s0 } & runsto p s0 Ok s1) (decreases pf) 
  = match pf with
  | ISL_Assign #pre #x #e ->
    let (st1, hp1) = s1 in
    assert (p == Assign x e);
    assert (exists (st_init:store). pre (st_init, hp1) /\ 
            st1 x == Nat (eval_expr (st_init, hp1) e) /\
            (forall y. y <> x ==> st1 y == st_init y));
    let st_init = FStar.IndefiniteDescription.indefinite_description_ghost 
                  store (fun st_i -> pre (st_i, hp1) 
                  /\ st1 x == Nat (eval_expr (st_i, hp1) e)
                  /\ (forall y. y <> x ==> st1 y == st_i y))
    in
    let s0 = (st_init, hp1) in
    assert (pre s0);
    let pf0 = R_Assign x e s0 in
    assert (forall y. fst (override st_init x (Nat (eval_expr s0 e)), snd s0) y == fst s1 y);
    let pf1 : runsto (Assign x e) s0 Ok s1 = R_Ext pf0 s0 s1 () () () () in
    (| s0, pf1 |)
  
  | ISL_Nondet #pre #x -> 
    let (st1, hp1) = s1 in
    assert (p == Nondet x);
    assert (exists v. pre (override st1 x v, hp1));
    let v = FStar.IndefiniteDescription.indefinite_description_ghost
              _ (fun v -> pre (override st1 x v, hp1)) in
    assert (pre (override st1 x v, hp1));
    let s0 = (override st1 x v, hp1) in
    assert (pre s0);
    let pf0 = R_Nondet s0 #x (st1 x) in
    let pf1 : runsto (Nondet x) s0 Ok s1 =
      R_Ext pf0 s0 s1 () () () ()
    in
    (|s0, pf1|)

  | ISL_Frame #p_pre #p_cmd #p_ok #p_er fr pf_p _ ->
    let (st1, hp1) = s1 in
    assert ((p_ok ** fr) s1); 

    let unfold p_two (h1:heap) (h2:heap) : prop = 
      heaps_disjoint h1 h2 /\ 
      hp1 == heap_union h1 h2 /\ 
      p_ok (st1, h1) /\ 
      fr (st1, h2)
    in
    assert (exists (h1:heap) (h2:heap). p_two h1 h2);
    
    lemma_exists_tuple p_two;
    let logic_parts (hp_tup : heap & heap) : prop = 
      p_two (fst hp_tup) (snd hp_tup) 
    in
    assert (exists (hp_tup: heap & heap). logic_parts hp_tup);
    
    let h_parts = FStar.IndefiniteDescription.indefinite_description_ghost (heap & heap) logic_parts in
    let h_ok = fst h_parts in
    let h_fr = snd h_parts in

    let (|s0_local, r_local|) = soundness_ok p_cmd p_pre p_ok p_er pf_p (st1, h_ok) in
    let (st0, hp0) = s0_local in

    assert (heaps_disjoint h_ok h_fr);
    lemma_runsto_disjoint h_fr r_local;
    assert (heaps_disjoint hp0 h_fr);

    let s0 : state = (st0, heap_union hp0 h_fr) in
    let r_global = r_frame r_local h_fr #() #() in

    assert (p_pre (st0, hp0));
    assert (fr (st1, h_fr)); 
    lemma_runsto_modifies r_local;
    assert (match_except_vars (modifies p_cmd) st0 st1);
    assert (fr (st0, h_fr));
    assert (snd s0 == heap_union hp0 h_fr);
    assert (heaps_disjoint hp0 h_fr /\ snd s0 == heap_union hp0 h_fr /\ p_pre (st0, hp0) /\ fr (st0, h_fr));
    
    assert (exists (h1 h2: heap). 
              heaps_disjoint h1 h2 /\ 
              snd s0 == heap_union h1 h2 /\ 
              p_pre (st0, h1) /\ 
              fr (st0, h2));
    assert ((p_pre ** fr) s0);
    (| s0, r_global |)

  | ISL_Skip -> 
    let s0 = s1 in
    let r = R_Skip s0 in
    (|s0, r|)
  
  | ISL_Error -> unreachable ()

  | ISL_Assume #pre #e ->
    assert (pre s1 /\ eval_expr s1 e == 0);
    let s0 = s1 in
    let r = R_Assume s0 #e () in
    (|s0, r|)

  | ISL_Seq #p #q #pre #mid_ok #mid_er #post_ok #post_er pf_p pf_q ->
    let (|s_mid, r_q|) = 
      soundness_ok q mid_ok post_ok post_er pf_q s1 in
    let (|s0, r_p|) =
      soundness_ok p pre mid_ok mid_er pf_p s_mid in
    let r = R_Seq r_p r_q in
    (|s0, r|)

  | ISL_ChoiceL #p #q #pre #post_ok #post_er pf_p ->
    let (|s0, r_p|) =
      soundness_ok p pre post_ok post_er pf_p s1 in
    let r = R_ChoiceL #p #q r_p in
    (|s0, r|)

  | ISL_ChoiceR #p #q #pre #post_ok #post_er pf_q -> 
    let (|s0, r_q|) =
      soundness_ok q pre post_ok post_er pf_q s1 in
    let r = R_ChoiceR #p #q r_q in
    (|s0, r|)

  | ISL_Kleene0 #p ->
    let s0 = s1 in
    let r = R_Kleene0 #p in
    (|s0, r|)

  | ISL_KleeneS #p #pre #post_ok #post_er pf_seq ->
    let (|s0, r_seq|) =
      soundness_ok (Seq (Kleene p) p) pre post_ok post_er pf_seq s1 in
    let r = R_KleeneS #p r_seq in
    (|s0, r|)
  
  | ISL_KleeneVariant #variant #p pf_var ->
    let n = FStar.IndefiniteDescription.indefinite_description_ghost
            _ (fun n -> variant n s1) in
    let rec aux (m : nat) (t : state { variant m t })
      : GTot (s0 : state { variant 0 s0 } & runsto (Kleene p) s0 Ok t) (decreases m) =
      if m = 0 then
        let s0 = t in
        let r = R_Kleene0 #p in
        (|s0, r|)
      else
        let m' = m - 1 in
        let pf_p = pf_var m' in
        let (|s_mid, r_p|) = 
          soundness_ok p (variant m') (variant (m' + 1)) (fun _ -> false) pf_p t in
        let (|s0, r_kleene|) = aux m' s_mid in
        let r = R_KleeneS #p (R_Seq r_kleene r_p) in
        (|s0, r|)
    in
    aux n s1
  
  | ISL_Empty #p -> unreachable ()
  
  | ISL_Consequence #pre #p #post_ok #post_er
    pre' post_ok' post_er' pf_p _ _ _ ->
    let (|s0, r|) = soundness_ok p pre post_ok post_er pf_p s1 in
    (|s0, r|)

  | ISL_Disjunction #pre1 #pre2 #p #post_ok1 #post_ok2
    #post_er1 #post_er2 pf_p1 pf_p2 ->
    if p2b (post_ok1 s1) then
      let (|s0, r|) = soundness_ok p pre1 post_ok1 post_er1 pf_p1 s1 in
      (|s0, r|)
    else (
      assert (post_ok2 s1);
      let (|s0, r|) = soundness_ok p pre2 post_ok2 post_er2 pf_p2 s1 in
      (|s0, r|)
    )

  | ISL_Alloc1 #x -> 
    let (st1, hp1) = s1 in
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
    assert (Full? (hp1 l));

    let st0 = st1 in
    let hp0 = override hp1 l Empty in
    let s0 : state = (st0, hp0) in
    let r_alloc = R_Alloc s0 #x l v #() in
    let r = R_Ext r_alloc s0 s1 () () () () in
    assert pre s0;
    (|s0, r|)

  | ISL_Alloc2 #x _ ->
    let (st1, hp1) = s1 in
    let unfold p_lv (l_i : loc) (v_i : value) : prop =
      st1 x == Loc l_i /\ points_to l_i v_i s1
    in
    lemma_exists_tuple p_lv;
    let logic_parts (lv : loc & value) : prop =
      p_lv (fst lv) (snd lv)
    in
    let lv_w = FStar.IndefiniteDescription.indefinite_description_ghost (loc & value) logic_parts in
    let l = fst lv_w in
    let v = snd lv_w in

    let st0 = st1 in
    let hp0 = override hp1 l Empty in
    let s0 : state = (st0, hp0) in
    let r_alloc = R_Alloc s0 #x l v in
    let r = R_Ext r_alloc s0 s1 () () () () in
    (|s0, r|)

  | ISL_Free #e -> 
    let (st1, hp1) = s1 in
    let l = eval_expr s1 e in
    let v = Nat 0 in

    let st0 = st1 in
    let hp0 = override hp1 l (Full v) in
    let s0 : state = (st0, hp0) in
    Classical.exists_intro (fun v -> points_to (eval_expr s0 e) v s0) v;
    let r_free = R_Free s0 e l in
    let hp1' = override hp0 l Empty in
    let r = R_Ext r_free s0 s1 () () () () in
    (|s0, r|)

  | ISL_FreeEr #e -> unreachable ()

  | ISL_FreeNull #e -> unreachable ()

  | ISL_Load #x #e ->
    let (st1, hp1) = s1 in
    let unfold p_lv (l_i : loc) (v_i : value) : prop =
      eval_expr s1 e == l_i /\ points_to l_i v_i s1 /\ st1 x == v_i
    in
    lemma_exists_tuple p_lv;
    let logic_parts (lv : loc & value) : prop = p_lv (fst lv) (snd lv) in
    let lv_w = FStar.IndefiniteDescription.indefinite_description_ghost (loc & value) logic_parts in
    let l = fst lv_w in
    let v = snd lv_w in
    let st0 = st1 in
    let hp0 = hp1 in
    let s0 : state = (st0, hp0) in
    Classical.exists_intro (fun v_i -> eval_expr s0 e == l /\ points_to l v_i s0) v;
    Classical.exists_intro (fun l_i -> exists v_i. eval_expr s0 e == l_i /\ points_to l_i v_i s0) l;
    let r_load = R_Load s0 x e l v in
    let st1' = override st0 x v in
    let r = R_Ext r_load s0 s1 () () () () in
    (|s0, r|)

  | ISL_LoadEr #x #e -> unreachable ()

  | ISL_LoadNull #x #e -> unreachable ()

  | ISL_Store #e1 #e2 -> 
    let (st1, hp1) = s1 in
    let p_l (l_i : loc) : prop =
      eval_expr s1 e1 == l_i /\ points_to l_i (Nat (eval_expr s1 e2)) s1
    in
    let l = FStar.IndefiniteDescription.indefinite_description_ghost loc p_l in
    let v_old = Nat 0 in
    let st0 = st1 in
    let hp0 = override hp1 l (Full v_old) in
    let s0 : state = (st0, hp0) in
    Classical.exists_intro (fun v_i -> eval_expr s0 e1 == l /\ points_to l v_i s0) v_old;
    Classical.exists_intro (fun l_i -> exists v_i. eval_expr s0 e1 == l_i /\ points_to l_i v_i s0) l;
    let r_store = R_Store s0 e1 e2 l v_old in
    let hp1' = override hp0 l (Full (Nat (eval_expr s0 e2))) in
    let r = R_Ext r_store s0 s1 () () () () in
    (|s0, r|)

  | ISL_StoreEr #e1 #e2 -> unreachable ()

  | ISL_StoreNull #e1 #e2 -> unreachable ()

and soundness_er
  (p : stmt) (pre : cond) (post_ok : cond) (post_er : cond)
  (pf : isl_triple pre p post_ok post_er)
  (s1 : state { post_er s1 })
  : GTot (s0 : state { pre s0 } & runsto p s0 Er s1) (decreases pf) 
  = match pf with
  | ISL_Assign #pre #x #e -> unreachable ()
  
  | ISL_Nondet #pre #x -> unreachable ()

  | ISL_Skip -> unreachable ()
  
  | ISL_Error ->
    let s0 = s1 in
    let r = R_Error s0 in
    (|s0, r|)

  | ISL_Assume #pre #e -> unreachable ()

  | ISL_Seq #p #q #pre #mid_ok #mid_er #post_ok #post_er pf_p pf_q ->
    if p2b (mid_er s1) then
      let (| s0, r |) = soundness_er p pre mid_ok mid_er pf_p s1 in
      (| s0, R_SeqEr #p #q r |)
    else (
      assert (post_er s1);
      let (| s_mid, r2 |) = soundness_er q mid_ok post_ok post_er pf_q s1 in
      assert (mid_ok s_mid);
      let (| s0, r1 |) = soundness_ok p pre mid_ok mid_er pf_p s_mid in
      (| s0, R_Seq #p #q r1 r2 |)
    )

  | ISL_ChoiceL #p #q #pre #post_ok #post_er pf_p ->
    let (|s0, r_p|) =
      soundness_er p pre post_ok post_er pf_p s1 in
    let r = R_ChoiceL #p #q r_p in
    (|s0, r|)

  | ISL_ChoiceR #p #q #pre #post_ok #post_er pf_q ->
    let (|s0, r_q|) =
      soundness_er q pre post_ok post_er pf_q s1 in
    let r = R_ChoiceR #p #q r_q in
    (|s0, r|)

  | ISL_Kleene0 -> unreachable ()

  | ISL_KleeneS #p #pre #post_ok #post_er pf_seq ->
    let (|s0, r_seq|) =
      soundness_er (Seq (Kleene p) p) pre post_ok post_er pf_seq s1 in
    let r = R_KleeneS #p r_seq in
    (|s0, r|)
  
  | ISL_KleeneVariant _ -> unreachable ()
  
  | ISL_Empty #p -> unreachable ()

  | ISL_Consequence #pre #p #post_ok #post_er
    pre' post_ok' post_er' pf_p _ _ _ ->
    let (|s0, r|) = soundness_er p pre post_ok post_er pf_p s1 in
    (|s0, r|)

  | ISL_Disjunction #pre1 #pre2 #p #post_ok1 #post_ok2
    #post_er1 #post_er2 pf_p1 pf_p2 ->
    if p2b (post_er1 s1) then
      let (|s0, r|) = soundness_er p pre1 post_ok1 post_er1 pf_p1 s1 in
      (|s0, r|)
    else (
      assert (post_er2 s1);
      let (|s0, r|) = soundness_er p pre2 post_ok2 post_er2 pf_p2 s1 in
      (|s0, r|)
    )

  | ISL_Frame #pre #p #post_ok #post_er fr pf_p _ ->
    let (st1, hp1) = s1 in
    let unfold p_two (h1 : heap) (h2 : heap) : prop =
      heaps_disjoint h1 h2 /\
      hp1 == heap_union h1 h2 /\
      post_er (st1, h1) /\
      fr (st1, h2)
    in
    lemma_exists_tuple p_two;
    let logic_parts (hp_tup : heap & heap) : prop =
      p_two (fst hp_tup) (snd hp_tup)
    in
    let h_parts = FStar.IndefiniteDescription.indefinite_description_ghost (heap & heap) logic_parts in
    let h_er = fst h_parts in
    let h_fr = snd h_parts in
    let (|s0_local, r_local|) = soundness_er p pre post_ok post_er pf_p (st1, h_er) in
    let (st0, hp0) = s0_local in
    assert (match_except_vars (fun _ -> True) st0 st1);
    lemma_runsto_disjoint h_fr r_local;
    let s0 : state = (st0, heap_union hp0 h_fr) in
    let r = r_frame r_local h_fr #() #() in

    lemma_runsto_modifies r_local; 
    assert (match_except_vars (modifies p) st0 st1);

    (|s0, r|)

  | ISL_Alloc1 #x -> unreachable ()

  | ISL_Alloc2 #x _ -> unreachable ()

  | ISL_Free #e -> unreachable ()

  | ISL_FreeEr #e ->
    let s0 = s1 in
    let l = eval_expr s0 e in
    let r = R_FreeEr s0 e l in
    (|s0, r|)

  | ISL_FreeNull #e ->
    let s0 = s1 in
    let r = R_FreeNull s0 e in
    (|s0, r|)

  | ISL_Load #x #e -> unreachable ()

  | ISL_LoadEr #x #e -> 
    let s0 = s1 in
    let l = eval_expr s0 e in
    let r = R_LoadEr s0 x e l in
    (|s0, r|)

  | ISL_LoadNull #x #e ->
    let s0 = s1 in
    let r = R_LoadNull s0 x e in
    (|s0, r|)

  | ISL_Store #e1 #e2 -> unreachable ()

  | ISL_StoreEr #e1 #e2 ->
    let s0 = s1 in
    let l = eval_expr s0 e1 in
    let r = R_StoreEr s0 e1 e2 l in
    (|s0, r|)

  | ISL_StoreNull #e1 #e2 ->
    let s0 = s1 in
    let r = R_StoreNull s0 e1 e2 in
    (|s0, r|) 

// type cond = state -> prop
// type term_mode = | Ok | Er

let soundness_ok2
  (p : stmt) (pre : cond) (post : term_mode -> cond)
  (pf : isl_triple pre p (post Ok) (post Er))
  (m : term_mode)
  (s1 : state { post m s1 })
  : GTot (s0 : state { pre s0 } & runsto p s0 m s1) (decreases pf) 
  = match m with
    | Ok -> soundness_ok p pre (post Ok) (post Er) pf s1
    | Er -> soundness_er p pre (post Ok) (post Er) pf s1

// strongest pre
let sp (p : stmt) (post : term_mode -> cond) : cond = magic()

let sp_ok (p : stmt) (post : term_mode -> cond)
  : isl_triple (sp p post) p (post Ok) (post Er) = magic()
