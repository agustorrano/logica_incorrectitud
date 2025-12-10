module IncLogic

open FStar.Mul

module S = FStar.StrongExcludedMiddle
module FE = FStar.FunctionalExtensionality
open FStar.FunctionalExtensionality { (^->) }

let test2 () =
  let f1 x = 1+x in
  let f2 x = x+1 in
  assert (forall x. f1 x == f2 x);
  assert (FE.feq f1 f2);
  assert (FE.on_domain int f1 == FE.on_domain int f2)

let test () =
  let f1 : (nat ^-> int) = FE.on_dom nat (fun x -> x <: int) in
  let f2 : (nat ^-> int) = FE.on_dom nat (fun x -> if x < 0 then -x else x) in
  // assert (forall (x:nat). f1 x == f2 x);
  assert (FE.feq #nat f1 f2);
  // assert (FE.on_domain nat f1 == FE.on_domain nat f2);
  assert (f1 == f2)

unfold
let p2b (p : prop) : GTot bool = S.strong_excluded_middle p

let unreachable #a (_ : squash False) : a = coerce_eq () ()

type var = string
type value = int

type expr =
  | Var : var -> expr
  | Const : int -> expr
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

type term_mode =
  | Ok
  | Er

type state = var -> int

let rec eval_expr (s : state) (e : expr) : GTot int =
  match e with
    | Var x -> s x
    | Const n -> n
    | Plus e1 e2 -> eval_expr s e1 + eval_expr s e2
    | Minus e1 e2 -> eval_expr s e1 - eval_expr s e2
    | Times e1 e2 -> eval_expr s e1 * eval_expr s e2
    | Eq e1 e2 -> if eval_expr s e1 = eval_expr s e2
                  then 0 else 1
    | Lt e1 e2 -> if eval_expr s e1 < eval_expr s e2
                  then 0 else 1
    | Gt e1 e2 -> if eval_expr s e1 > eval_expr s e2
                  then 0 else 1

let override (#a : eqtype) (#b : Type) (f : a -> b) (x : a) (y : b) : a -> b =
  fun z -> if z = x then y else f z

// Semántica del lenguaje
noeq
type runsto : (p : stmt) -> (s0 : state) -> (m : term_mode) -> (s1 : state) -> Type0 =
  (* no-op, sólo reescribe los estados. Si usáramos funciones
     extensionales para state (i.e. ^->) tendríamos
     la igualdad s0 == s0' y no haría falta esta regla. *)
  | R_Ext : #p:stmt -> #s0:state -> #m:term_mode -> #s1:state ->
    runsto p s0 m s1 ->
    s0' : state ->
    s1' : state ->
    (#_ : squash (forall x. s0 x == s0' x)) ->
    (#_ : squash (forall x. s1 x == s1' x)) ->
    runsto p s0' m s1'

  | R_Assign : s : state ->
    #x : var -> #e : expr ->
    runsto (Assign x e) s Ok (override s x (eval_expr s e))
  | R_Nondet : s : state -> #x : var -> v : value ->
    runsto (Nondet x) s Ok (override s x v)
  | R_Skip : s : state -> runsto Skip s Ok s
  | R_Error : s : state -> runsto Error s Er s
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
    m : term_mode -> t : state ->
    v : value ->
    runsto p (override s x v) m t ->
    runsto (Local x p) s m (fun y -> if x = y then s y else t y)

let init : state = fun _ -> 0

// let pf1 : runsto (Local "y" (Assign "x" (Var "y")))
//                  init
//                  Ok
//                  (override init "x" 1)
//  = R_Local init Ok (override init "x" 1) 1
//      _

type cond = state -> prop

// Lógica de incorrectitud
noeq
type il_triple : (pre : cond) -> (p : stmt) -> (post_ok : cond) -> (post_er : cond) -> Type =
  | I_Assign : #pre:cond -> #x : var -> #e : expr ->
    il_triple pre (Assign x e)
      (fun s -> exists x_init. pre (override s x x_init)
                                /\ (s x = eval_expr (override s x x_init) e))
      (fun s -> false)

  | I_Nondet : #x : var -> #pre : cond ->
    il_triple pre (Nondet x) (fun s ->
      exists v. pre (override s x v)) (fun s -> false)

  // | I_Local : 

  | I_Skip : pre : cond -> 
    il_triple pre Skip pre (fun s -> false)

  | I_Error : pre : cond -> 
    il_triple pre Error (fun s -> false) pre

  | I_Assume : pre : cond -> #e : expr ->
    il_triple pre (Assume e) (fun s -> pre s /\ eval_expr s e == 0) (fun s -> false)

  | I_Seq : #p : stmt -> #q : stmt ->
    #pre : cond -> #mid_ok : cond -> #mid_er : cond -> 
    #post_ok : cond -> #post_er : cond ->
    il_triple pre p mid_ok mid_er ->
    il_triple mid_ok q post_ok post_er ->
    il_triple pre (Seq p q) post_ok (fun s -> mid_er s \/ post_er s)

  //| I_Choice : #p : stmt -> #q : stmt -> #pre : cond -> 
  //  #post_okp : cond -> #post_erp : cond ->
  //  #post_okq : cond -> #post_erq : cond ->
  //  il_triple pre p post_okp post_erp ->
  //  il_triple pre q post_okq post_erq ->
  //  il_triple pre (Choice p q) 
  //    (fun s -> post_okp s \/ post_okq s)
  //    (fun s -> post_erp s \/ post_erq s)

  // Equivalente a la de arriba (esta es la versión del paper):
  | I_ChoiceL : #p : stmt -> #q : stmt ->
    #pre : cond -> #post_ok : cond -> #post_er : cond ->
    il_triple pre p post_ok post_er ->
    il_triple pre (Choice p q) post_ok post_er
  
  | I_ChoiceR : #p : stmt -> #q : stmt ->
    #pre : cond -> #post_ok : cond -> #post_er : cond ->
    il_triple pre q post_ok post_er ->
    il_triple pre (Choice p q) post_ok post_er

  | I_Kleene0 :
    #p : stmt -> #pre : cond -> 
    il_triple pre (Kleene p) pre (fun s -> false)

  | I_KleeneS :
    #p : stmt -> #pre : cond -> #post_ok : cond -> #post_er : cond ->
    il_triple pre (Seq (Kleene p) p) post_ok post_er ->
    il_triple pre (Kleene p) post_ok post_er

  | I_KleeneVariant :
    #variant : (nat -> cond) -> #p : stmt ->
    (n : nat ->
      il_triple (variant n) p (variant (n + 1)) (fun s -> false)) ->
    il_triple (variant 0) (Kleene p) (fun s -> exists n. variant n s) (fun s -> false)
  
  | I_Empty : #pre : cond -> #p : stmt -> 
    il_triple pre p (fun s -> false) (fun s -> false)
  
  | I_Consequence : #pre : cond -> #p : stmt -> 
    #post_ok : cond -> #post_er : cond -> 
    pre' : cond -> post_ok' : cond -> post_er' : cond ->
    il_triple pre p post_ok post_er ->
    squash (forall x. pre x ==> pre' x) ->
    squash (forall x. post_ok' x ==> post_ok x) ->
    squash (forall x. post_er' x ==> post_er x) ->
    il_triple pre' p post_ok' post_er'
  
  | I_Disjunction : #pre1 : cond -> #pre2 : cond -> 
    #p : stmt -> #post_ok1 : cond -> #post_ok2 : cond -> 
    #post_er1 : cond -> #post_er2 : cond ->
    il_triple pre1 p post_ok1 post_er1 ->
    il_triple pre2 p post_ok2 post_er2 ->
    il_triple (fun s -> pre1 s \/ pre2 s) p 
      (fun s -> post_ok1 s \/ post_ok2 s) 
      (fun s -> post_er1 s \/ post_er2 s)

// let _ : (x:int & y:int{x > y}) = (|3,2|)

// let hd (l : list int {Cons? l}) : int =
//   match l with
//   | hd::tl -> hd

let rec soundness_ok
  (p : stmt) (pre : cond) (post_ok : cond) (post_er : cond)
  (pf : il_triple pre p post_ok post_er)
  (s1 : state { post_ok s1 })
  : GTot (s0 : state { pre s0 } & runsto p s0 Ok s1) (decreases pf) =
  match pf with
  | I_Assign #pre #x #e -> 
    admit()

  | I_Nondet #x #pre ->
    assert (p == Nondet x);
    // Existe v tal que pre s1[v/x]
    assert (exists v. pre (override s1 x v));
    // Tomar ese v.
    let v = FStar.IndefiniteDescription.indefinite_description_ghost
              _ (fun v -> pre (override s1 x v)) in
    assert (pre (override s1 x v));
    let s0 = override s1 x v in
    assert (pre s0);
    // ^ Conseguimos un estado inicial.

    // Dado que podemos elegir el valor que toma x, elijamos (s1 x).
    // Entonces es claro que terminamos en s1, como necesitamos.
    let pf0 : runsto (Nondet x) s0 Ok (override s0 x (s1 x)) =
      R_Nondet s0 #x (s1 x)
    in
    // Solamente hay que aplicar extensionalidad...
    let pf1 : runsto (Nondet x) s0 Ok s1 =
      R_Ext pf0 _ _
    in
    (|s0, pf1|)

  | I_Skip _ -> 
    let s0 = s1 in
    let r = R_Skip s0 in
    (|s0, r|)

  | I_Error _ -> unreachable ()

  | I_Assume pre #e ->
    assert (pre s1 /\ eval_expr s1 e == 0);
    let s0 = s1 in
    let r = R_Assume s0 #e () in
    (|s0, r|)

  | I_Seq #p #q #pre #mid_ok #mid_er #post_ok #post_er pf_p pf_q ->
    let (|s_mid, r_q|) = 
      soundness_ok q mid_ok post_ok post_er pf_q s1 in
    let (|s0, r_p|) =
      soundness_ok p pre mid_ok mid_er pf_p s_mid in
    let r = R_Seq r_p r_q in
    (|s0, r|)
  
  | I_ChoiceL #p #q #pre #post_ok #post_er pf_p ->
    let (|s0, r_p|) =
      soundness_ok p pre post_ok post_er pf_p s1 in
    let r = R_ChoiceL #p #q r_p in
    (|s0, r|)
  
  | I_ChoiceR #p #q #pre #post_ok #post_er pf_q ->
    let (|s0, r_q|) =
      soundness_ok q pre post_ok post_er pf_q s1 in
    let r = R_ChoiceR #p #q r_q in
    (|s0, r|)

  | I_Kleene0 #p ->
    let s0 = s1 in
    let r = R_Kleene0 #p in
    (|s0, r|)
  
  | I_KleeneS #p #pre #post_ok #post_er pf_seq ->
    let (|s0, r_seq|) =
      soundness_ok (Seq (Kleene p) p) pre post_ok post_er pf_seq s1 in
    let r = R_KleeneS #p r_seq in
    (|s0, r|)

  | I_KleeneVariant #variant #p pf_var -> 
    admit()

  | I_Empty -> unreachable ()

  | I_Consequence #pre #p #post_ok #post_er
    pre' post_ok' post_er' pf_p _ _ _ -> 
    let (|s0, r|) = soundness_ok p pre post_ok post_er pf_p s1 in
    (|s0, r|)
  
  | I_Disjunction #pre1 #pre2 #p #post_ok1 #post_ok2
    #post_er1 #post_er2 pf_p1 pf_p2 ->
    if p2b (post_ok1 s1) then
      let (|s0, r|) = soundness_ok p pre1 post_ok1 post_er1 pf_p1 s1 in
      (|s0, r|)
    else (
      assert (post_ok2 s1);
      let (|s0, r|) = soundness_ok p pre2 post_ok2 post_er2 pf_p2 s1 in
      (|s0, r|)
    )

and soundness_er
  (p : stmt) (pre : cond) (post_ok : cond) (post_er : cond)
  (pf : il_triple pre p post_ok post_er)
  (s1 : state { post_er s1 })
  : GTot (s0 : state { pre s0 } & runsto p s0 Er s1)
         (decreases pf)
   =
  match pf with
  | I_Assign -> unreachable ()
  | I_Nondet -> unreachable ()
  | I_Skip _ -> unreachable ()
  | I_Assume _ -> unreachable ()

  | I_Error _ -> 
    let s0 = s1 in
    let r = R_Error s0 in
    (|s0, r|)

  | I_Seq #p #q #pre #mid_ok #mid_er #post_ok #post_er pf_p pf_q ->
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

  | I_ChoiceL #p #q #pre #post_ok #post_er pf_p ->
    let (|s0, r_p|) =
      soundness_er p pre post_ok post_er pf_p s1 in
    let r = R_ChoiceL #p #q r_p in
    (|s0, r|)
  
  | I_ChoiceR #p #q #pre #post_ok #post_er pf_q ->
    let (|s0, r_q|) =
      soundness_er q pre post_ok post_er pf_q s1 in
    let r = R_ChoiceR #p #q r_q in
    (|s0, r|)

  | I_Kleene0 -> unreachable ()
  
  | I_KleeneS #p #pre #post_ok #post_er pf_seq ->
    let (|s0, r_seq|) =
      soundness_er (Seq (Kleene p) p) pre post_ok post_er pf_seq s1 in
    let r = R_KleeneS #p r_seq in
    (|s0, r|)

  | I_KleeneVariant _ -> unreachable ()

  | I_Empty -> unreachable ()

  | I_Consequence #pre #p #post_ok #post_er
    pre' post_ok' post_er' pf_p _ _ _ -> 
    let (|s0, r|) = soundness_er p pre post_ok post_er pf_p s1 in
    (|s0, r|)
  
  | I_Disjunction #pre1 #pre2 #p #post_ok1 #post_ok2
    #post_er1 #post_er2 pf_p1 pf_p2 ->
    if p2b (post_er1 s1) then
      let (|s0, r|) = soundness_er p pre1 post_ok1 post_er1 pf_p1 s1 in
      (|s0, r|)
    else (
      assert (post_er2 s1);
      let (|s0, r|) = soundness_er p pre2 post_ok2 post_er2 pf_p2 s1 in
      (|s0, r|)
    )
