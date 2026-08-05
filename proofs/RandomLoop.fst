module RandomLoop

open IncSepLogic
open FStar.Classical

// Utils
let ( ||| ) = Choice
let enot (e : expr) : expr = Minus (Const 1) e
let ge (x y : expr) : expr = enot (Lt x y)

// Def del programa a verificar
(*
n := 1000000;
i, j := 0;
while (i < n){
  i++;
  if (random()) j++;
}
assert  (j != n);
*)

let init_vars = 
  Assign "n" (Const 1000000) `Seq`
  (Assign "i" (Const 0) `Seq`
  Assign "j" (Const 0))

let loop_body =
  Assume (Lt (Var "i") (Var "n")) `Seq`
  (Assign "i" (Plus (Var "i") (Const 1)) `Seq`
  (Assign "j" (Plus (Var "j") (Const 1)) ||| Skip))

let assert_stmt =
  Seq (Assume (Eq (Var "j") (Var "n"))) Error |||
  Assume (enot (Eq (Var "j") (Var "n")))

let prog1 =
  (Seq init_vars
       (Seq (Kleene loop_body)
            (Seq (Assume (Eq (Var "i") (Var "n"))) assert_stmt)))

// Estados y condiciones
let pre_init : cond =
  fun _ -> true

let post_er_bug : cond =
  fun (st, _, m) -> st "n" == Nat 1000000 /\ st "i" == Nat 1000000 /\ st "j" == Nat 1000000 /\ m == Er

let mid_i (k : nat) : cond =
  fun (st, _, m) -> k < 1000000 /\ st "n" == Nat 1000000 /\ st "i" == Nat (k + 1) /\ st "j" == Nat k /\ m == Ok

let variant (k : nat) : cond = 
  fun (st, _, m) -> k <= 1000000 /\ st "n" == Nat 1000000 /\ st "i" == Nat k /\ st "j" == Nat k /\ m == Ok

let pre_assign (k : nat) : cond = 
  fun s -> variant k s /\ eval_expr s (Lt (Var "i") (Var "n")) =!= 0 /\ s._3 == Ok

let pre_assert : cond = 
  fun s -> exists (k : nat). variant k s

// Lemas auxiliares
let lemma_p_i_consequence (k : nat) (s : state) : Lemma 
  (requires mid_i k s)
  (ensures (is_ok (fun s ->
      exists (st_init : var -> value). 
        pre_assign k (st_init, s._2, s._3) /\ 
        s._1 "i" == Nat (eval_expr (st_init, s._2, s._3) (Plus (Var "i") (Const 1))) /\
        (forall y. y <> "i" ==> s._1 y == st_init y)) s)) =
  let st, hp, m = s in
  let st_init = override st "i" (Nat k) in
  let s_init = (st_init, hp, m) in
  let p_exist (st_i : var -> value) : prop =
    pre_assign k (st_i, hp, m) /\ 
    st "i" == Nat (eval_expr (st_i, hp, m) (Plus (Var "i") (Const 1))) /\
    (forall y. y <> "i" ==> st y == st_i y)
  in
  Classical.exists_intro p_exist st_init

let lemma_p_j_consequence (k:nat) (s:state) : Lemma 
  (requires variant (k + 1) s)
  (ensures (is_ok (fun s ->
      exists (st_init : var -> value). 
        mid_i k (st_init, s._2, s._3) /\ 
        s._1 "j" == Nat (eval_expr (st_init, s._2, s._3) (Plus (Var "j") (Const 1))) /\
        (forall y. y <> "j" ==> s._1 y == st_init y)) s)) =
  let st, hp, m = s in
  let st_init = override st "j" (Nat k) in
  let s_init = (st_init, hp, m) in
  let p_exist (st_i : var -> value) : prop =
    mid_i k (st_i, hp, m) /\ 
    st "j" == Nat (eval_expr (st_i, hp, m) (Plus (Var "j") (Const 1))) /\
    (forall y. y <> "j" ==> st y == st_i y)
  in
  Classical.exists_intro p_exist st_init

let proof_loop_step (k : nat) : isl_triple (is_ok (variant k)) loop_body (variant (k + 1)) =
  let p_assumed = ISL_Assume #(variant k) (Lt (Var "i") (Var "n")) in

  let p_i_raw = ISL_Assign #(pre_assign k) "i" (Plus (Var "i") (Const 1)) in
  let pf_i = Classical.forall_intro (Classical.move_requires (lemma_p_i_consequence k)) in
  let p_i = ISL_Consequence (pre_assign k) (mid_i k) p_i_raw () pf_i in

  let p_j_raw = ISL_Assign #(mid_i k) "j" (Plus (Var "j") (Const 1)) in
  let pf_j = Classical.forall_intro (Classical.move_requires (lemma_p_j_consequence k)) in
  let p_j_branch = ISL_Consequence (mid_i k) (variant (k + 1)) p_j_raw () pf_j in
  
  let p_j = ISL_ChoiceL p_j_branch in
  let p_ij = ISL_Seq p_i p_j in

  let mid_assumed : cond = fun s -> variant k s /\ eval_expr s (Lt (Var "i") (Var "n")) =!= 0 in
  let expected_post_ij : cond = fun s -> variant (k + 1) s \/ s._3 == Er /\ mid_i k s in

  let p_ij_adapted = 
    ISL_Consequence #(pre_assign k) (is_ok mid_assumed) expected_post_ij p_ij () () 
  in
  
  let p_raw = ISL_Seq p_assumed p_ij_adapted in
  ISL_Consequence (variant k) (variant (k + 1)) p_raw () ()

let lemma_kleene : isl_triple (kleene_pre variant) (Kleene loop_body) (kleene_post variant) =
  let step (n : nat) =
    ISL_Consequence
      (variant n)
      (variant (n + 1))
      (proof_loop_step n)
      () ()
  in 
  ISL_KleeneVariant #variant #loop_body step

let mid_n (s : state) : prop =
  s._3 == Ok /\ s._1 "n" == Nat 1000000

// Demostraciones formales
let proof_init : isl_triple (is_ok pre_init) init_vars (kleene_pre variant) =
  let p_n_raw = ISL_Assign #pre_init "n" (Const 1000000) in
  let p_n = ISL_Consequence pre_init mid_n p_n_raw () () in

  let p_i = ISL_Assign #_ "i" (Const 0) in
  let p_j = ISL_Assign #_ "j" (Const 0) in
  
  let p_ij = ISL_Seq p_i p_j in
  let p_init = ISL_Seq p_n p_ij in
  ISL_Consequence pre_init (kleene_pre variant) p_init () ()

let proof_assert : isl_triple (is_ok pre_assert) (Seq (Assume (Eq (Var "i") (Var "n"))) assert_stmt) post_er_bug =
  let p_exit_raw = ISL_Assume #pre_assert (Eq (Var "i") (Var "n")) in
  let p_exit = ISL_Consequence pre_assert (variant 1000000) p_exit_raw () () in
  
  let p_cond_err_raw = ISL_Assume #(variant 1000000) (Eq (Var "j") (Var "n")) in
  let pre_error_state : cond = fun s -> variant 1000000 s /\ eval_expr s (Eq (Var "j") (Var "n")) =!= 0 in
  let p_cond_err = ISL_Consequence (variant 1000000) pre_error_state p_cond_err_raw () () in
  let p_err_raw = ISL_Error #pre_error_state in
  
  let p_branch_err_raw = ISL_Seq p_cond_err p_err_raw in
  let p_branch_err = ISL_Consequence (variant 1000000) post_er_bug p_branch_err_raw () () in
  
  let p_assert = ISL_ChoiceL p_branch_err in
  let p_raw = ISL_Seq p_exit p_assert in
  ISL_Consequence pre_assert post_er_bug p_raw () ()

let proof_prog1 : isl_triple (is_ok pre_init) prog1 post_er_bug =
  let adapted_assert = ISL_Consequence (kleene_post variant) post_er_bug proof_assert () () in
  let p_kleene_assert_raw = ISL_Seq lemma_kleene adapted_assert in
  let p_kleene_assert = ISL_Consequence (kleene_pre variant) post_er_bug p_kleene_assert_raw () () in
  
  let p_raw = ISL_Seq proof_init p_kleene_assert in
  ISL_Consequence pre_init post_er_bug p_raw () ()
