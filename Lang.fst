module Lang

open FStar.Mul

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

let rec eval_expr (s : state) (e : expr) : int =
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
  | R_Seq_Er : #p : stmt -> #q : stmt ->
    #s : state -> #t : state ->
    runsto p s Er t -> runsto (Seq p q) s Er t
  | R_Seq : #p : stmt -> #q : stmt -> #m : term_mode ->
    #s : state -> #t : state -> #u : state ->
    runsto p s Ok t -> runsto q t m u ->
    runsto (Seq p q) s m u
  | R_Choice_L : #p : stmt -> #q : stmt ->
    #s : state -> #m : term_mode -> #t : state ->
    runsto p s m t -> runsto (Choice p q) s m t
  | R_Choice_R : #p : stmt -> #q : stmt ->
    #s: state -> #m : term_mode -> #t : state ->
    runsto q s m t -> runsto (Choice p q) s m t
  | R_Kleene_Zero : #p : stmt -> #s : state -> 
    runsto (Kleene p) s Ok s
  | R_Kleene_Step : #p : stmt -> #s : state ->
    #m : term_mode -> #t : state -> q : stmt ->
    runsto (Seq (Kleene p) q) s m t ->
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
    il_triple pre (Nondet x) (fun s -> exists v. pre (override s x v)) (fun s -> false)

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

  | I_Choice : #p : stmt -> #q : stmt -> #pre : cond -> 
    #post_okp : cond -> #post_erp : cond ->
    #post_okq : cond -> #post_erq : cond ->
    il_triple pre p post_okp post_erp ->
    il_triple pre q post_okq post_erq ->
    il_triple pre (Choice p q) 
      (fun s -> post_okp s \/ post_okq s)
      (fun s -> post_erp s \/ post_erq s)

  // Equivalente a la de arriba (esta es la versión del paper):
  // | I_Choice1 : #p : stmt -> #q : stmt ->
  //   #pre : cond -> #post_ok : cond -> #post_er : cond ->
  //   il_triple pre p post_ok post_er ->
  //   il_triple pre (Choice p q) post_ok post_er
  // | I_Choice2 : #p : stmt -> #q : stmt ->
  //   #pre : cond -> #post_ok : cond -> #post_er : cond ->
  //   il_triple pre q post_ok post_er ->
  //   il_triple pre (Choice p q) post_ok post_er

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


let test : (x:int & y:int{x > y}) = (|3,2|)

// Si se complica por el 'if' en el refinamiento, considerar las dos de abajo
let soundness
  (p : stmt) (pre : cond) (post_ok : cond) (post_er : cond)
  (m : term_mode)
  (pf : il_triple pre p post_ok post_er)
  (s1 : state { if m = Ok then post_ok s1 else post_er s1 })
  : (s0 : state { pre s0 } & runsto p s0 m s1) =
  admit()

let soundness_ok
  (p : stmt) (pre : cond) (post_ok : cond) (post_er : cond)
  (pf : il_triple pre p post_ok post_er)
  (s1 : state { post_ok s1 })
  : (s0 : state { pre s0 } & runsto p s0 Ok s1) =
  admit()

let soundness_er
  (p : stmt) (pre : cond) (post_ok : cond) (post_er : cond)
  (pf : il_triple pre p post_ok post_er)
  (s1 : state { post_er s1 })
  : (s0 : state { pre s0 } & runsto p s0 Er s1) =
  admit()
