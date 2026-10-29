module IncLogicCollapsed

// A parallel presentation of IncLogic with one terminal error point.
// Normal stores are retained; an error carries no store at all.
//
// The comparison is about derivability, not an assumed completeness theorem:
// erase_derivation translates every IncLogic proof, and lift_derivation
// reconstructs a precise postcondition from every collapsed proof.
// In particular, the error-only equivalence requires a NONEMPTY precise
// error postcondition.  The empty postcondition is always vacuous.

module I = IncLogic

noeq
type state =
  | Normal : I.store -> state
  | Failed : state

type precond = I.store -> prop
type cond = state -> prop

unfold let normal (p : precond) : cond = function
  | Normal st -> p st
  | Failed -> False

unfold let normal_part (q : cond) : precond = fun st -> q (Normal st)
unfold let lift_pre (p : precond) : I.cond = fun s -> p s._1 /\ s._2 == I.Ok
unfold let old_pre (p : I.cond) : precond = fun st -> p (st, I.Ok)

let collapse (s : I.state) : state =
  match s._2 with
  | I.Ok -> Normal s._1
  | I.Er -> Failed

// Direct image along collapse, rather than replacing an error post by True
// on every original store (which would not be sound in incorrectness logic).
unfold let erase (q : I.cond) : cond = function
  | Normal st -> q (st, I.Ok)
  | Failed -> exists (st : I.store). q (st, I.Er)

unfold let represents (q : cond) (precise : I.cond) : prop =
  forall s. q s <==> erase precise s

unfold let seq_post (mid post : cond) : cond = fun s ->
  post s \/ (match s with | Normal _ -> False | Failed -> mid Failed)

// Like IncLogic.kleene_post, the variant rule collects normal outcomes.
// Error outcomes are derived separately using C_KleeneS and C_Seq.
unfold let iteration_post (variant : nat -> cond) : cond =
  normal (fun st -> exists (n : nat). variant n (Normal st))

// These rules mention only collapsed predicates.  In particular, C_Error
// records only whether the precondition is inhabited, and C_Seq propagates
// the single Failed point without a final store.
noeq
type il_triple : precond -> I.stmt -> cond -> Type =
  | C_Assign : #pre : precond -> #x : I.var -> #e : I.expr ->
    il_triple pre (I.Assign x e)
      (normal (fun st -> exists v.
        pre (I.override st x v) /\
        st x == I.eval_expr' (I.override st x v) e))
  | C_Nondet : #pre : precond -> #x : I.var ->
    il_triple pre (I.Nondet x)
      (normal (fun st -> exists v. pre (I.override st x v)))
  | C_Skip : pre : precond -> il_triple pre I.Skip (normal pre)
  | C_Error : pre : precond -> il_triple pre I.Error
      (fun s -> match s with
        | Normal _ -> False
        | Failed -> exists (st : I.store). pre st)
  | C_Assume : pre : precond -> #e : I.expr ->
    il_triple pre (I.Assume e)
      (normal (fun st -> pre st /\ I.eval_expr' st e =!= 0))
  | C_Seq : #p : I.stmt -> #q : I.stmt -> #pre : precond -> #mid : cond -> #post : cond ->
    il_triple pre p mid -> il_triple (normal_part mid) q post ->
    il_triple pre (I.Seq p q) (seq_post mid post)
  | C_ChoiceL : #p : I.stmt -> #q : I.stmt -> #pre : precond -> #post : cond ->
    il_triple pre p post -> il_triple pre (I.Choice p q) post
  | C_ChoiceR : #p : I.stmt -> #q : I.stmt -> #pre : precond -> #post : cond ->
    il_triple pre q post -> il_triple pre (I.Choice p q) post
  | C_Kleene0 : #p : I.stmt -> #pre : precond ->
    il_triple pre (I.Kleene p) (normal pre)
  | C_KleeneS : #p : I.stmt -> #pre : precond -> #post : cond ->
    il_triple pre (I.Seq (I.Kleene p) p) post ->
    il_triple pre (I.Kleene p) post
  | C_KleeneVariant : #variant : (nat -> cond) -> #p : I.stmt ->
    (n : nat -> il_triple (normal_part (variant n)) p
      (normal (normal_part (variant (n + 1))))) ->
    il_triple (normal_part (variant 0)) (I.Kleene p) (iteration_post variant)
  | C_Consequence : #pre : precond -> #p : I.stmt -> #post : cond ->
    pre' : precond -> post' : cond -> il_triple pre p post ->
    squash (forall st. pre st ==> pre' st) ->
    squash (forall s. post' s ==> post s) -> il_triple pre' p post'
  | C_Disjunction : #pre1 : precond -> #pre2 : precond -> #p : I.stmt ->
    #post1 : cond -> #post2 : cond ->
    il_triple pre1 p post1 -> il_triple pre2 p post2 ->
    il_triple (fun st -> pre1 st \/ pre2 st) p (fun s -> post1 s \/ post2 s)

// Forget the stores in the error part of an existing derivation.
let rec erase_derivation
  (#pre #post : I.cond) (#p : I.stmt) (pf : I.il_triple pre p post)
  : Tot (il_triple (old_pre pre) p (erase post)) (decreases pf) =
  match pf with
  | I.I_Assign #pre #x #e ->
    C_Consequence _ _ (C_Assign #(old_pre pre) #x #e) () ()
  | I.I_Nondet #x #pre ->
    C_Consequence _ _ (C_Nondet #(old_pre pre) #x) () ()
  | I.I_Skip pre -> C_Consequence _ _ (C_Skip (old_pre pre)) () ()
  | I.I_Error pre -> C_Consequence _ _ (C_Error (old_pre pre)) () ()
  | I.I_Assume pre #e ->
    C_Consequence _ _ (C_Assume (old_pre pre) #e) () ()
  | I.I_Seq #p #q #pre #mid #post pf_p pf_q ->
    let left = erase_derivation pf_p in
    let right = C_Consequence (normal_part (erase mid)) (erase post)
      (erase_derivation pf_q) () () in
    C_Consequence _ _ (C_Seq left right) () ()
  | I.I_ChoiceL #p #q pf_p ->
    C_Consequence _ _ (C_ChoiceL #p #q (erase_derivation pf_p)) () ()
  | I.I_ChoiceR #p #q pf_q ->
    C_Consequence _ _ (C_ChoiceR #p #q (erase_derivation pf_q)) () ()
  | I.I_Kleene0 #p #pre ->
    C_Consequence _ _ (C_Kleene0 #p #(old_pre pre)) () ()
  | I.I_KleeneS #p pf_seq ->
    C_Consequence _ _ (C_KleeneS #p (erase_derivation pf_seq)) () ()
  | I.I_KleeneVariant #variant #p steps ->
    let step (n : nat)
      : Tot (il_triple (normal_part (erase (variant n))) p
          (normal (normal_part (erase (variant (n + 1)))))) =
      C_Consequence _ _ (erase_derivation (steps n)) () () in
    C_Consequence _ _ (C_KleeneVariant #(fun n -> erase (variant n)) #p step) () ()
  | I.I_Consequence #pre #p #post pre' post' pf_p _ _ ->
    C_Consequence _ _ (erase_derivation pf_p) () ()
  | I.I_Disjunction pf_p pf_q ->
    C_Consequence _ _
      (C_Disjunction (erase_derivation pf_p) (erase_derivation pf_q)) () ()

// The chosen precise post is part of the result.  It agrees with the
// collapsed post on EVERY normal store and on existence of an error store.
type lifting (pre : precond) (p : I.stmt) (post : cond) =
  precise : I.cond { represents post precise } &
    I.il_triple (I.is_ok (lift_pre pre)) p precise

let rec lift_derivation
  (#pre : precond) (#p : I.stmt) (#post : cond)
  (pf : il_triple pre p post)
  : Tot (lifting pre p post) (decreases pf) =
  match pf with
  | C_Assign #pre #x #e ->
    let precise = I.is_ok (fun s -> exists v.
      pre (I.override s._1 x v) /\
      s._1 x == I.eval_expr' (I.override s._1 x v) e) in
    (|precise, I.I_Consequence _ precise
      (I.I_Assign #(lift_pre pre) #x #e) () ()|)
  | C_Nondet #pre #x ->
    let precise = I.is_ok (fun s -> exists v. pre (I.override s._1 x v)) in
    (|precise, I.I_Consequence _ precise
      (I.I_Nondet #x #(lift_pre pre)) () ()|)
  | C_Skip pre ->
    (|I.is_ok (lift_pre pre), I.I_Skip (lift_pre pre)|)
  | C_Error pre ->
    let precise : I.cond = fun s -> s._2 == I.Er /\ pre s._1 in
    (|precise, I.I_Consequence _ precise (I.I_Error (lift_pre pre)) () ()|)
  | C_Assume pre #e ->
    let precise = I.is_ok (fun s -> pre s._1 /\ I.eval_expr' s._1 e =!= 0) in
    (|precise, I.I_Consequence _ precise (I.I_Assume (lift_pre pre) #e) () ()|)
  | C_Seq #p #q #pre #mid #post pf_p pf_q ->
    let (|mid', left|) = lift_derivation pf_p in
    let (|post', right|) = lift_derivation pf_q in
    let right' = I.I_Consequence mid' post' right () () in
    let precise : I.cond = fun s -> post' s \/ (s._2 == I.Er /\ mid' s) in
    (|precise, I.I_Seq left right'|)
  | C_ChoiceL #p #q pf_p ->
    let (|precise, proof|) = lift_derivation pf_p in
    (|precise, I.I_ChoiceL #p #q proof|)
  | C_ChoiceR #p #q pf_q ->
    let (|precise, proof|) = lift_derivation pf_q in
    (|precise, I.I_ChoiceR #p #q proof|)
  | C_Kleene0 #p #pre ->
    (|I.is_ok (lift_pre pre), I.I_Kleene0 #p #(lift_pre pre)|)
  | C_KleeneS #p pf_seq ->
    let (|precise, proof|) = lift_derivation pf_seq in
    (|precise, I.I_KleeneS #p proof|)
  | C_KleeneVariant #variant #p steps ->
    let precise_variant (n : nat) : I.cond =
      lift_pre (normal_part (variant n)) in
    let step (n : nat)
      : Tot (I.il_triple (I.is_ok (precise_variant n)) p
          (I.is_ok (precise_variant (n + 1)))) =
      let (|q, proof|) = lift_derivation (steps n) in
      I.I_Consequence (precise_variant n) (I.is_ok (precise_variant (n + 1)))
        proof () () in
    let precise = I.kleene_post precise_variant in
    let proof = I.I_Consequence _ precise
      (I.I_KleeneVariant #precise_variant #p step) () () in
    (|precise, proof|)
  | C_Consequence #pre #p #post pre' post' pf_p _ _ ->
    let (|q, proof|) = lift_derivation pf_p in
    // Keep only the requested normal outcomes.  For Failed, keep the
    // already justified precise error witnesses if that point is requested.
    let precise : I.cond = fun s -> q s /\ post' (collapse s) in
    (|precise, I.I_Consequence (lift_pre pre') precise proof () ()|)
  | C_Disjunction #pre1 #pre2 #p #post1 #post2 pf_p pf_q ->
    let (|q1, proof1|) = lift_derivation pf_p in
    let (|q2, proof2|) = lift_derivation pf_q in
    let precise : I.cond = fun s -> q1 s \/ q2 s in
    (|precise, I.I_Consequence _ precise
      (I.I_Disjunction proof1 proof2) () ()|)

// The general equivalence, as a proposition about inhabited proof types.
unfold let derivable (pre : precond) (p : I.stmt) (post : cond) : prop =
  exists (_ : il_triple pre p post). True

unfold let original_derivable (pre : precond) (p : I.stmt) (post : I.cond) : prop =
  exists (_ : I.il_triple (I.is_ok (lift_pre pre)) p post). True

let derivability_iff (pre : precond) (p : I.stmt) (post : cond)
  : Lemma (derivable pre p post <==>
      (exists (q : I.cond). represents post q /\ original_derivable pre p q)) =
  if t2b (derivable pre p post) then (
    let pf = FStar.IndefiniteDescription.indefinite_description_ghost
      (il_triple pre p post) (fun _ -> True) in
    let (|q, proof|) = lift_derivation pf in
    assert (original_derivable pre p q)
  ) else if t2b (exists (q : I.cond).
      represents post q /\ original_derivable pre p q) then (
    let q = FStar.IndefiniteDescription.indefinite_description_ghost I.cond
      (fun q -> represents post q /\ original_derivable pre p q) in
    let proof = FStar.IndefiniteDescription.indefinite_description_ghost
      (I.il_triple (I.is_ok (lift_pre pre)) p q) (fun _ -> True) in
    let pf = C_Consequence pre post (erase_derivation proof) () () in
    assert (derivable pre p post)
  )

unfold let error_post : cond = function
  | Normal _ -> False
  | Failed -> True

unfold let er (q : precond) : I.cond = fun s -> s._2 == I.Er /\ q s._1

// Explicit proof transformations for the error-only instance.
let error_to_precise (#pre : precond) (#p : I.stmt)
  (pf : il_triple pre p error_post)
  : Tot (q : precond { exists st. q st } &
      I.il_triple (I.is_ok (lift_pre pre)) p (er q)) =
  let (|precise, proof|) = lift_derivation pf in
  let q : precond = fun st -> precise (st, I.Er) in
  (|q, I.I_Consequence (lift_pre pre) (er q) proof () ()|)

let precise_to_error (#pre : precond) (#p : I.stmt)
  (q : precond { exists st. q st })
  (proof : I.il_triple (I.is_ok (lift_pre pre)) p (er q))
  : il_triple pre p error_post =
  C_Consequence pre error_post (erase_derivation proof) () ()

// Specialize derivability_iff to error_post, then normalize the precise
// postcondition to er q.  Representation at Failed gives nonemptiness.
let error_derivability_iff (pre : precond) (p : I.stmt)
  : Lemma (derivable pre p error_post <==>
      (exists (q : precond).
        (exists st. q st) /\ original_derivable pre p (er q))) =
  derivability_iff pre p error_post;
  if t2b (derivable pre p error_post) then (
    let precise = FStar.IndefiniteDescription.indefinite_description_ghost I.cond
      (fun precise -> represents error_post precise /\
        original_derivable pre p precise) in
    let proof = FStar.IndefiniteDescription.indefinite_description_ghost
      (I.il_triple (I.is_ok (lift_pre pre)) p precise) (fun _ -> True) in
    let q : precond = fun st -> precise (st, I.Er) in
    let proof' = I.I_Consequence (lift_pre pre) (er q) proof () () in
    assert (exists st. q st);
    assert (original_derivable pre p (er q))
  ) else if t2b (exists (q : precond).
      (exists st. q st) /\ original_derivable pre p (er q)) then (
    let q = FStar.IndefiniteDescription.indefinite_description_ghost precond
      (fun q -> (exists st. q st) /\ original_derivable pre p (er q)) in
    assert (represents error_post (er q));
    assert (exists (precise : I.cond).
      represents error_post precise /\ original_derivable pre p precise)
  )

// Operational meaning: the quotient keeps each normal store and identifies
// all error stores.  Its input is always a normal store.
noeq
type runsto (p : I.stmt) (st : I.store) : state -> Type0 =
  | R_Collapse : #s : I.state -> I.runsto p (st, I.Ok) s ->
    runsto p st (collapse s)

let soundness (#pre : precond) (#p : I.stmt) (#post : cond)
  (pf : il_triple pre p post) (s : state { post s })
  : GTot (st : I.store { pre st } & runsto p st s) =
  let (|precise, proof|) = lift_derivation pf in
  let target : (t : I.state { precise t /\ collapse t == s }) =
    match s with
    | Normal st -> (st, I.Ok)
    | Failed ->
      let st = FStar.IndefiniteDescription.indefinite_description_ghost I.store
        (fun st -> precise (st, I.Er)) in
      (st, I.Er) in
  let (|initial, execution|) = I.soundness p (I.is_ok (lift_pre pre))
    precise proof target in
  (|initial._1, R_Collapse execution|)

// A checked counterexample to omitting nonemptiness: Skip has a derivable
// empty error postcondition, but cannot derive the collapsed error point.
let skip_empty_error (pre : precond)
  : I.il_triple (I.is_ok (lift_pre pre)) I.Skip (er (fun _ -> False)) =
  I.I_Consequence (lift_pre pre) (er (fun _ -> False))
    (I.I_Skip (lift_pre pre)) () ()

let skip_only_normal (#s0 #s1 : I.state) (r : I.runsto I.Skip s0 s1)
  : Lemma (s1._2 == I.Ok) =
  match r with
  | I.R_Skip _ -> ()

let skip_no_collapsed_error (pre : precond)
  : Lemma (~(derivable pre I.Skip error_post)) =
  if t2b (derivable pre I.Skip error_post) then (
    let pf = FStar.IndefiniteDescription.indefinite_description_ghost
      (il_triple pre I.Skip error_post) (fun _ -> True) in
    let (|q, proof|) = error_to_precise pf in
    let st = FStar.IndefiniteDescription.indefinite_description_ghost I.store q in
    let (|_, execution|) = I.soundness I.Skip (I.is_ok (lift_pre pre))
      (er q) proof (st, I.Er) in
    skip_only_normal execution
  )
