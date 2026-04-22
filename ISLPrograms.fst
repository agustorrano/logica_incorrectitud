module ISLPrograms

open IncSepLogic

open FStar.Classical

(*
n := 1000000;
i, j := 0;
while (i <= n){
  i++;
  if (random()) j++;
}
assert  (j != n);
*)

let ( ||| ) = Choice

let enot (e : expr) : expr = Minus (Const 1) e
let ge (x y : expr) : expr = enot (Lt x y)

// n := 1000000; i := 0; j := 0;
unfold let init_vars = 
  Assign "n" (Const 1000000) `Seq`
  (Assign "i" (Const 0) `Seq`
  Assign "j" (Const 0))

// el cuerpo del while
let loop_body =
  Assume (Lt (Var "i") (Var "n")) `Seq`
  (Assign "i" (Plus (Var "i") (Const 1)) `Seq`
  (Assign "j" (Plus (Var "j") (Const 1)) ||| Skip))

let assert_stmt =
  Seq (Assume (Eq (Var "j") (Var "n"))) Error |||
  Assume (enot (Eq (Var "j") (Var "n")))

unfold let prog1 =
  init_vars `Seq`
  Kleene loop_body `Seq`
  Assume (ge (Var "i") (Var "n")) `Seq`
  assert_stmt

let cond_false : cond =
  fun _ -> false

// estado inicial
let pre_vacia : cond =
  fun _ -> true

let post_er_bug : cond =
  fun (st, hp) -> st "n" == Nat 1000000 /\ st "i" == Nat 1000000 /\ st "j" == Nat 1000000

unfold let state_k (k : nat) : cond =
  fun (st, hp) -> st "n" == Nat 1000000 /\ st "i" == Nat k /\ st "j" == Nat k

unfold let mid_i (k : nat) : cond =
  fun (st, hp) -> st "n" == Nat 1000000 /\ st "i" == Nat (k + 1) /\ st "j" == Nat k

// prueba init_vars
let test_init () : GTot (isl_triple pre_vacia init_vars (state_k 0) cond_false) =
  let p_n = ISL_Assign #pre_vacia "n" (Const 1000000) in
  let p_i = ISL_Assign #_ "i" (Const 0) in
  let p_j = ISL_Assign #_ "j" (Const 0) in

  let p_ij = ISL_Seq p_i p_j in
  let p_init = ISL_Seq p_n p_ij in

  ISL_Consequence pre_vacia (state_k 0) cond_false p_init () () ()

let lemma_inc_i (k : nat) (x : state)
  : Lemma (requires (mid_i k x))
          (ensures (let st, hp = x in
                    exists (x_init : store). state_k k (x_init, hp) /\
                    st "i" == Nat (eval_expr (x_init, hp) (Plus (Var "i") (Const 1))) /\
                    (forall y. y <> "i" ==> st y == x_init y))) =
  let st, hp = x in
  let x_init : store = fun y ->
    if y = "i" then Nat k
    else st y
  in

  exists_intro (fun x_init ->
    state_k k (x_init, hp) /\
    st "i" == Nat (eval_expr (x_init, hp) (Plus (Var "i") (Const 1))) /\
    (forall y. y <> "i" ==> st y == x_init y)) x_init

let lemma_inc_j (k : nat) (x : state)
  : Lemma (requires (state_k (k + 1) x))
          (ensures (let st, hp = x in
                    exists x_init. mid_i k (x_init, hp) /\
                    st "j" == Nat (eval_expr (x_init, hp) (Plus (Var "j") (Const 1))) /\
                    (forall y. y <> "j" ==> st y == x_init y))) =
  let st, hp = x in
  let x_init : store = fun y ->
    if y = "j" then Nat k
    else st y
  in

  exists_intro (fun x_init ->
    mid_i k (x_init, hp) /\
    st "j" == Nat (eval_expr (x_init, hp) (Plus (Var "j") (Const 1))) /\
    (forall y. y <> "j" ==> st y == x_init y)) x_init

let test_1step (k : nat{k < 1000000}) : GTot (isl_triple (state_k k) loop_body (state_k (k + 1)) cond_false) =
  let p_assume_raw = ISL_Assume #(state_k k) (Lt (Var "i") (Var "n")) in
  let p_assume = ISL_Consequence (state_k k) (state_k k) cond_false p_assume_raw () () () in

  let p_i_raw = ISL_Assign #(state_k k) "i" (Plus (Var "i") (Const 1)) in
  let _ = forall_intro (move_requires (lemma_inc_i k)) in
  let p_i = ISL_Consequence (state_k k) (mid_i k) cond_false p_i_raw () () () in

  let p_j_raw = ISL_Assign #(mid_i k) "j" (Plus (Var "j") (Const 1)) in
  let _ = forall_intro (move_requires (lemma_inc_j k)) in
  let p_j_branch = ISL_Consequence (mid_i k) (state_k (k + 1)) cond_false p_j_raw () () () in
  let p_j = ISL_ChoiceL p_j_branch in

  let p_ij = ISL_Seq p_i p_j in
  let p_raw = ISL_Seq p_assume p_ij in
  ISL_Consequence (state_k k) (state_k (k + 1)) cond_false p_raw () () ()

let rec test_loop (k : nat{k <= 1000000}) : GTot (isl_triple (state_k 0) (Kleene loop_body) (state_k k) cond_false) =
  if k = 0 then
    let p_base = ISL_Kleene0 #loop_body #(state_k 0) in
    ISL_Consequence (state_k 0) (state_k k) cond_false p_base () () ()
  
  else
    let p_prev = test_loop (k - 1) in
    let p_step = test_1step (k - 1) in

    let p_seq_raw = ISL_Seq p_prev p_step in
    let p_seq = ISL_Consequence (state_k 0) (state_k k) cond_false p_seq_raw () () () in
    ISL_KleeneS p_seq

let test_assert () : GTot (isl_triple (state_k 1000000) (Seq (Assume (Eq (Var "i") (Var "n"))) assert_stmt) cond_false post_er_bug) =
  let p_exit_raw = ISL_Assume #(state_k 1000000) (Eq (Var "i") (Var "n")) in
  let p_exit = ISL_Consequence (state_k 1000000) (state_k 1000000) cond_false p_exit_raw () () () in

  let p_cond_err = ISL_Assume #(state_k 1000000) (Eq (Var "j") (Var "n")) in
  let p_err = ISL_Error #_ in
  let p_branch_err = ISL_Seq p_cond_err p_err in

  let p_assert = ISL_ChoiceL p_branch_err in
  let p_raw = ISL_Seq p_exit p_assert in
  ISL_Consequence (state_k 1000000) cond_false post_er_bug p_raw () () ()

let test1 () : GTot (isl_triple pre_vacia
  (Seq init_vars
       (Seq (Kleene loop_body)
            (Seq (Assume (Eq (Var "i") (Var "n"))) assert_stmt)))
                 cond_false
                 post_er_bug) =
  let triple_seq =
    ISL_Seq (test_init ())
            (ISL_Seq (test_loop 1000000)
                     (test_assert ()))
  in
  ISL_Consequence pre_vacia cond_false post_er_bug triple_seq () () ()

(*
  {true}
  x = alloc()
  *x = 1
  {er: x=NULL}
*)
(*
  x = alloc()
  free(x)
*)
