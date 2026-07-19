module IncLogicOne

module FE = FStar.FunctionalExtensionality
open FStar.FunctionalExtensionality { (^->) }

let unreachable #a (_ : squash False) : a = coerce_eq () ()

type var = string
type value = nat

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

type term_mode =
  | Ok
  | Er

type store = var -> value
type state = store & term_mode
type cond = state -> prop

let rec eval_expr' (s : store) (e : expr) : GTot nat =
  match e with
    | Var x -> s x
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

// Semántica del lenguaje
noeq
type runsto : (p : stmt) -> (s0 : state) -> (s1 : state) -> Type0 =
  | R_Ext : #p:stmt -> #s0:state -> #s1:state ->
    runsto p s0 s1 -> s0' : state -> s1' : state ->
    (#_ : squash (forall x. s0._1 x == s0'._1 x /\
                  s0._2 == s0'._2)) ->
    (#_ : squash (forall x. s1._1 x == s1'._1 x /\
                  s1._2 == s1'._2)) ->
    runsto p s0' s1'
    
  | R_Assign : s : state{s._2 == Ok} ->
    #x : var -> #e : expr ->
    runsto (Assign x e) s (override s._1 x (eval_expr s e), s._2)

  | R_Nondet : s : state{s._2 == Ok} -> #x : var -> v : value ->
    runsto (Nondet x) s (override s._1 x v, s._2)

  | R_Skip : s : state{s._2 == Ok} -> runsto Skip s s

  | R_Error : s : state{s._2 == Ok} -> runsto Error s (s._1, Er)

  | R_Assume : s : state{s._2 == Ok} -> #e : expr -> 
    squash (eval_expr s e =!= 0) ->
    runsto (Assume e) s s

  | R_SeqEr : #p : stmt -> #q : stmt ->
    #s : state{s._2 == Ok} -> #t : state{t._2 == Er} ->
    runsto p s t -> runsto (Seq p q) s t

  | R_Seq : #p : stmt -> #q : stmt ->
    #s : state{s._2 == Ok} -> #t : state{t._2 == Ok} -> #u : state ->
    runsto p s t -> runsto q t u ->
    runsto (Seq p q) s u

  | R_ChoiceL : #p : stmt -> #q : stmt ->
    #s : state{s._2 == Ok} -> #t : state ->
    runsto p s t -> runsto (Choice p q) s t

  | R_ChoiceR : #p : stmt -> #q : stmt ->
    #s: state{s._2 == Ok} -> #t : state ->
    runsto q s t -> runsto (Choice p q) s t

  | R_Kleene0 : #p : stmt -> #s : state{s._2 == Ok} -> 
    runsto (Kleene p) s s
  
  | R_KleeneS : #p : stmt -> #s : state{s._2 == Ok} -> #t : state ->
    runsto (Seq (Kleene p) p) s t ->
    runsto (Kleene p) s t

let init : state = ((fun _ -> 0), Ok)

unfold let is_ok (c : cond) : cond = fun s -> c s /\ s._2 == Ok

unfold
let kleene_pre (variant : nat -> cond) : cond =
  is_ok (variant 0)

unfold
let kleene_post (variant : nat -> cond) : cond =
  fun s -> exists (n : nat). variant n s /\ (n == 0 ==> s._2 == Ok)

// Lógica de incorrectitud
noeq
type il_triple : (pre : cond) -> (p : stmt) -> (post : cond) -> Type =
  | I_Assign : #pre : cond -> #x : var -> #e : expr ->
    il_triple (is_ok pre) (Assign x e)
      (is_ok (fun s -> exists x_init. 
        pre ((override s._1 x x_init), s._2) /\ 
        (s._1 x = eval_expr ((override s._1 x x_init), s._2) e)))

  | I_Nondet : #x : var -> #pre : cond ->
    il_triple (is_ok pre) (Nondet x) 
      (is_ok (fun s ->
        exists v. pre ((override s._1 x v), s._2)))

  | I_Skip : pre : cond -> 
    il_triple (is_ok pre) Skip (is_ok pre)

  | I_Error : pre : cond -> 
    il_triple (is_ok pre) Error 
      (fun s -> let (st, m) = s in m == Er /\ pre (st, Ok))

  | I_Assume : pre : cond -> #e : expr ->
    il_triple (is_ok pre) (Assume e)
      (is_ok (fun s -> pre s /\ eval_expr s e =!= 0))

  | I_Seq : #p : stmt -> #q : stmt ->
    #pre : cond -> #mid : cond -> #post : cond ->
    il_triple (is_ok pre) p mid ->
    il_triple (is_ok mid) q post ->
    il_triple (is_ok pre) (Seq p q) 
      (fun s -> post s \/ (s._2 == Er /\ mid s))

  | I_ChoiceL : #p : stmt -> #q : stmt ->
    #pre : cond -> #post : cond ->
    il_triple (is_ok pre) p post ->
    il_triple (is_ok pre) (Choice p q) post
  
  | I_ChoiceR : #p : stmt -> #q : stmt ->
    #pre : cond -> #post : cond ->
    il_triple (is_ok pre) q post ->
    il_triple (is_ok pre) (Choice p q) post

  | I_Kleene0 :
    #p : stmt -> #pre : cond -> 
    il_triple (is_ok pre) (Kleene p) (is_ok pre)

  | I_KleeneS :
    #p : stmt -> #pre : cond -> #post : cond ->
    il_triple (is_ok pre) (Seq (Kleene p) p) post ->
    il_triple (is_ok pre) (Kleene p) post

  | I_KleeneVariant :
    #variant : (nat -> cond) -> #p : stmt ->
    (n : nat ->
      il_triple (is_ok (variant n)) p (variant (n + 1))) ->
    il_triple (kleene_pre variant) (Kleene p) (kleene_post variant)
  
  | I_Consequence : #pre : cond -> #p : stmt -> 
    #post : cond -> pre' : cond -> post' : cond ->
    il_triple (is_ok pre) p post ->
    squash (forall x. pre x ==> pre' x) ->
    squash (forall x. post' x ==> post x) ->
    il_triple (is_ok pre') p post'
  
  | I_Disjunction : #pre1 : cond -> #pre2 : cond -> 
    #p : stmt -> #post1 : cond -> #post2 : cond -> 
    il_triple (is_ok pre1) p post1 ->
    il_triple (is_ok pre2) p post2 ->
    il_triple (is_ok (fun s -> pre1 s \/ pre2 s)) p 
      (fun s -> post1 s \/ post2 s)

let rec soundness
  (p : stmt) (pre : cond) (post : cond)
  (pf : il_triple pre p post)
  (s1 : state { post s1 })
  : GTot (s0 : state { pre s0 } & runsto p s0 s1) (decreases pf) 
  = match pf with
  | I_Assign #pre #x #e ->
    let (st1, m) = s1 in
    assert (p == Assign x e);
    assert (exists x_init. pre ((override st1 x x_init), m) 
            /\ (st1 x = eval_expr ((override st1 x x_init), m) e));
    let x_init = FStar.IndefiniteDescription.indefinite_description_ghost 
                 _ (fun x_init -> pre ((override st1 x x_init), m) 
                    /\ (st1 x = eval_expr ((override st1 x x_init), m) e))
    in
    assert (pre ((override st1 x x_init), m) 
            /\ (st1 x = eval_expr ((override st1 x x_init), m) e));
    let st0 = override st1 x x_init in
    let s0 = (st0, Ok) in
    assert (pre s0);
    let pf0 = R_Assign s0 #x #e in
    assert (forall y. override st0 x (eval_expr s0 e) y == st1 y);
    let pf1 : runsto (Assign x e) s0 s1 = R_Ext pf0 s0 s1 in
    (| s0, pf1 |)

  | I_Nondet #x #pre ->
    let (st1, m) = s1 in
    assert (p == Nondet x);
    assert (exists v. pre ((override st1 x v), m));
    let v = FStar.IndefiniteDescription.indefinite_description_ghost
              _ (fun v -> pre ((override st1 x v), m)) in
    assert (pre ((override st1 x v), m));
    let st0 = override st1 x v in
    let s0 = (st0, Ok) in
    assert (pre s0);
    let pf0 : runsto (Nondet x) s0 ((override st0 x (st1 x)), Ok) =
      R_Nondet s0 #x (st1 x)
    in
    let pf1 : runsto (Nondet x) s0 s1 =
      R_Ext pf0 _ _
    in
    (|s0, pf1|)

  | I_Skip _ -> 
    let s0 = s1 in
    let r = R_Skip s0 in
    (|s0, r|)

  | I_Error _ -> 
    let (st1, _) = s1 in
    let s0 = (st1, Ok) in
    let r = R_Error s0 in
    (|s0, r|)

  | I_Assume pre #e ->
    assert (pre s1 /\ eval_expr s1 e =!= 0);
    let s0 = s1 in
    let r = R_Assume s0 #e () in
    (|s0, r|)

  | I_Seq #p #q #pre #mid #post pf_p pf_q ->
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
  
  | I_ChoiceL #p #q #pre #post pf_p ->
    let (|s0, r_p|) =
      soundness p (is_ok pre) post pf_p s1 in
    let r = R_ChoiceL #p #q #s0 #s1 r_p in
    (|s0, r|)
  
  | I_ChoiceR #p #q #pre #post pf_q ->
    let (|s0, r_q|) =
      soundness q (is_ok pre) post pf_q s1 in
    let r = R_ChoiceR #p #q #s0 #s1 r_q in
    (|s0, r|)

  | I_Kleene0 #p ->
    let s0 = s1 in
    let r = R_Kleene0 #p in
    (|s0, r|)
  
  | I_KleeneS #p #pre #post pf_seq ->
    let (|s0, r_seq|) =
      soundness (Seq (Kleene p) p) (is_ok pre) post pf_seq s1 in
    let r = R_KleeneS #p r_seq in
    (|s0, r|)

  | I_KleeneVariant #variant #p pf_var ->
    let p_n (n:nat) : prop = variant n s1 /\ (n == 0 ==> s1._2 == Ok) in
    assert (exists n. p_n n);
    let n = FStar.IndefiniteDescription.indefinite_description_ghost
              _ p_n in
    assert (variant n s1);
    let rec aux (m : nat) (t : state { variant m t /\ (m == 0 ==> t._2 == Ok) })
      : GTot (s0 : state { variant 0 s0 /\ s0._2 == Ok } & runsto (Kleene p) s0 t) (decreases m) =
      if m = 0 then
        let s0 = t in
        let r = R_Kleene0 #p in
        (| s0, r |)
      else 
        let m' = m - 1 in
        let pf_p = pf_var m' in
        let (| s_mid, r_p |) =
          soundness p (is_ok (variant m')) (variant (m' + 1)) pf_p t in
        let (| s0, r_kleene |) = aux m' s_mid in
        let r = R_KleeneS #p (R_Seq r_kleene r_p) in
        (| s0, r |)
    in
    aux n s1


  | I_Consequence #pre #p #post pre' post' pf_p _ _ -> 
    let (|s0, r|) = soundness p (is_ok pre) post pf_p s1 in
    (|s0, r|)
  
  | I_Disjunction #pre1 #pre2 #p #post1 #post2 pf_p1 pf_p2 ->
    if t2b (post1 s1) then
      let (|s0, r|) = soundness p (is_ok pre1) post1 pf_p1 s1 in
      (|s0, r|)
    else (
      assert (post2 s1);
      let (|s0, r|) = soundness p (is_ok pre2) post2 pf_p2 s1 in
      (|s0, r|)
    )
