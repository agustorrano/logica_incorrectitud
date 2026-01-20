module IncSepLogic

open FStar.Mul

module S = FStar.StrongExcludedMiddle
module FE = FStar.FunctionalExtensionality
open FStar.FunctionalExtensionality { (^->) }

unfold
let p2b (p : prop) : GTot bool = S.strong_excluded_middle p

let unreachable #a (_ : squash False) : a = coerce_eq () ()

type var = string
type loc = nat
type value = 
  | Int of int 
  | Loc of loc

type store = var -> value
type heap = loc -> option value

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
  | Alloc : var -> stmt
  | Free : expr -> stmt
  | Load : var -> expr -> stmt
  | Store : expr -> expr -> stmt

type term_mode =
  | Ok
  | Er

type state = store & heap

type cond = state -> prop

let rec eval_expr (s : state) (e : expr) : GTot int =
  let (st, hp) = s in
  match e with
    | Var x -> (
      match st x with
        | Int n -> n
        | Loc l -> l <: int
      )
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
  | R_Skip : s : state -> runsto Skip s Ok s
  | R_Error : s : state -> runsto Error s Er s
  | R_Assign : x : var -> 
    e : expr -> s : state -> 
    runsto (Assign x e) s Ok (let (st, hp) = s in
    override st x (Int (eval_expr s e)), hp)
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
  // |[ L : x := alloc()]|ok = {(σ, (s[x |-> l], h[l |-> v])) | 
  // σ = (s, h) ∧ v ∈ Val /\ (l ∉ dom(h) \/ h(l) = ⊥)}
  | R_Alloc : s : state -> #x : var -> l : loc -> 
    #(squash (snd s l == None)) ->
    runsto (Alloc x) s Ok (let (st, hp) = s in
    override st x (Loc l), override hp l (Some (Int 0)))
  // |[ L : free(x)]|ok = {(σ, (s, h[s(x) |-> ⊥])) | σ = (s, h) ∧ h(s(x)) ∈ Val}
  | R_Free : s : state -> e : expr -> l : loc ->
    #(squash (eval_expr s e == l)) ->
    #(squash (snd s l <> None)) ->
    runsto (Free e) s Ok (let (st, hp) = s in
    st, override hp l None)
    // |[L : free(x)]|er(L') = {(σ, σ) | L = L' /\ σ = (s, h) ∧ (s(x) = null \/ h(s(x)) = ⊥)}
  | R_FreeEr : s : state -> e : expr -> l : loc ->
    #(squash (eval_expr s e == l)) ->
    #(squash (snd s l == None)) ->
    runsto (Free e) s Er s
  // |[L : x := [y]]|ok = {(σ, (s, h[x |-> v])) | σ = (s, h) ∧ h(s(y)) = v ∈ Val}
  | R_Load : s : state -> x : var -> e : expr ->
    l : loc -> v : value ->
    #(squash (snd s l == Some v)) ->
    #(squash (eval_expr s e == l)) ->
    runsto (Load x e) s Ok (let (st, hp) = s in
    override st x v, hp)
  // |[L : x := [y]]|er(L') = {(σ, σ) | L = L' /\ σ = (s, h) ∧ (s(x) = null \/ h(s(x)) = ⊥)}
  | R_LoadEr : s : state -> x : var -> 
    e : expr -> l : loc ->
    #(squash (eval_expr s e == l)) ->
    #(squash (snd s l == None)) ->
    runsto (Load x e) s Er s
  // |[L : [x] := y]|ok = {(σ, (s, h[s(x) |-> s(y)])) | σ = (s, h) ∧ h(s(x)) ∈ Val}
  | R_Store : s : state -> e1 : expr -> e2 : expr ->
    l : loc -> v : value ->
    #(squash (snd s l == Some v)) ->
    #(squash (eval_expr s e1 == l)) ->
    runsto (Store e1 e2) s Ok (let (st, hp) = s in
    st, override hp l (Some (Int (eval_expr s e2))))
  // |[L : [x] := y]|er(L') = {(σ, σ) | L = L' /\ σ = (s, h) ∧ (s(x) = null \/ h(s(x)) = ⊥)}
  | R_StoreEr : s : state -> e1 : expr ->
    e2 : expr -> l : loc ->
    #(squash (eval_expr s e1 == l)) ->
    #(squash (snd s l == None)) ->
    runsto (Store e1 e2) s Er s

