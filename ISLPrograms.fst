module ISLPrograms

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
while (i <= n){
  i++;
  if (random()) j++;
}
assert  (j != n);
*)

unfold let init_vars = 
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

unfold let prog1 =
  init_vars `Seq`
  Kleene loop_body `Seq`
  Assume (ge (Var "i") (Var "n")) `Seq`
  assert_stmt

// Estados y condiciones
unfold let cond_false : cond =
  fun _ -> false

let pre_vacia : cond =
  fun _ -> true

let post_er_bug : cond =
  fun (st, _) -> st "n" == Nat 1000000 /\ st "i" == Nat 1000000 /\ st "j" == Nat 1000000

unfold let mid_i (k : nat) : cond =
  fun (st, _) -> k < 1000000 /\ st "n" == Nat 1000000 /\ st "i" == Nat (k + 1) /\ st "j" == Nat k

unfold let variant (n : nat) : cond = 
  fun (st, _) -> n <= 1000000 /\ st "n" == Nat 1000000 /\ st "i" == Nat n /\ st "j" == Nat n

unfold let pre_assign (k : nat) : cond = 
  fun s -> variant k s /\ eval_expr s (Lt (Var "i") (Var "n")) == 0

unfold let pre_assert : cond = 
  fun s -> exists (k : nat). variant k s

// Lemas auxiliares
let lemma_p_i_consequence (k:nat{k < 1000000}) (s:state)
  : Lemma (requires mid_i k s)
          (ensures (let st, hp = s in
                   exists st_init. pre_assign k (st_init, hp) /\
                   st "i" == Nat (eval_expr (st_init, hp) (Plus (Var "i") (Const 1))) /\
                   (forall y. y <> "i" ==> st y == st_init y))) =
  let st, hp = s in
  let st_init = fun y -> if y = "i" then Nat k else st y in
  let s_init = (st_init, hp) in
  
  assert (eval_expr s_init (Var "i") == k)

let lemma_p_j_consequence (k:nat{k < 1000000}) (s:state)
  : Lemma (requires variant (k + 1) s)
          (ensures (let st, hp = s in
                   exists st_init. mid_i k (st_init, hp) /\
                   st "j" == Nat (eval_expr (st_init, hp) (Plus (Var "j") (Const 1))) /\
                   (forall y. y <> "j" ==> st y == st_init y))) =
  let st, hp = s in
  let st_init = fun y -> if y = "j" then Nat k else st y in
  let s_init = (st_init, hp) in

  assert (eval_expr s_init (Var "j") == k)

let lemma_bounded_kleene (#variant : nat -> cond) (#bound : nat) (#p : stmt)
  (bounded_step : (k:nat{k < bound} -> GTot (isl_triple (variant k) p (variant (k + 1)) cond_false)))
  : GTot (isl_triple (variant 0) (Kleene p) (fun s -> exists (k:nat{k <= bound}). variant k s) cond_false) =
  let variant_total (n:nat) : cond =
    if n <= bound then variant n else cond_false
  in

  let total_step (n:nat) : GTot (isl_triple (variant_total n) p (variant_total (n + 1)) cond_false) =
    if n < bound then
      let p_b = bounded_step n in
      ISL_Consequence (variant_total n) (variant_total (n+1)) cond_false p_b () () ()
    else
      let p_empty = ISL_Empty #p in
      ISL_Consequence (variant_total n) (variant_total (n+1)) cond_false p_empty () () ()
  in

  let p_kleene = ISL_KleeneVariant #variant_total #p total_step in
  ISL_Consequence (variant 0) (fun s -> exists (k:nat{k <= bound}). variant k s) cond_false p_kleene () () ()

// Demostraciones formales
let proof_init : isl_triple pre_vacia init_vars (variant 0) cond_false =
  let p_n = ISL_Assign #pre_vacia "n" (Const 1000000) in
  let p_i = ISL_Assign #_ "i" (Const 0) in
  let p_j = ISL_Assign #_ "j" (Const 0) in

  let p_ij = ISL_Seq p_i p_j in
  let p_init = ISL_Seq p_n p_ij in

  ISL_Consequence pre_vacia (variant 0) cond_false p_init () () ()

let proof_loop_step (k : nat{k < 1000000}) : GTot (isl_triple (variant k) loop_body (variant (k + 1)) cond_false) =
  let p_assume = ISL_Assume #(variant k) (Lt (Var "i") (Var "n")) in
  let p_assumed = ISL_Consequence (variant k) (pre_assign k) cond_false p_assume () () () in

  let p_i_raw = ISL_Assign #(pre_assign k) "i" (Plus (Var "i") (Const 1)) in
  let _ = forall_intro (move_requires (lemma_p_i_consequence k)) in
  let p_i = ISL_Consequence (pre_assign k) (mid_i k) cond_false p_i_raw () () () in

  let p_j_raw = ISL_Assign #(mid_i k) "j" (Plus (Var "j") (Const 1)) in
  let _ = forall_intro (move_requires (lemma_p_j_consequence k)) in
  let p_j_branch = ISL_Consequence (mid_i k) (variant (k + 1)) cond_false p_j_raw () () () in
  let p_j = ISL_ChoiceL p_j_branch in

  let p_ij = ISL_Seq p_i p_j in
  let p_raw = ISL_Seq p_assumed p_ij in
  ISL_Consequence (variant k) (variant (k + 1)) cond_false p_raw () () ()

let proof_loop () : GTot (isl_triple (variant 0) (Kleene loop_body) (fun s -> exists (k:nat). variant k s) cond_false) =
  let p_bounded = lemma_bounded_kleene #variant #1000000 #loop_body proof_loop_step in
  ISL_Consequence (variant 0) (fun s -> exists (k:nat). variant k s) cond_false p_bounded () () ()

let proof_assert () : GTot (isl_triple pre_assert (Seq (Assume (Eq (Var "i") (Var "n"))) assert_stmt) cond_false post_er_bug) =
  let p_exit_raw = ISL_Assume #pre_assert (Eq (Var "i") (Var "n")) in
  let _ = forall_intro (fun s -> move_requires (fun s -> assert (variant 1000000 s)) s) in
  let p_exit = ISL_Consequence pre_assert (variant 1000000) cond_false p_exit_raw () () () in

  let p_cond_err = ISL_Assume #(variant 1000000) (Eq (Var "j") (Var "n")) in
  let p_err = ISL_Error #_ in
  let p_branch_err = ISL_Seq p_cond_err p_err in

  let p_assert = ISL_ChoiceL p_branch_err in
  let p_raw = ISL_Seq p_exit p_assert in
  ISL_Consequence pre_assert cond_false post_er_bug p_raw () () ()

let proof_prog1 () : GTot (isl_triple pre_vacia
  (Seq init_vars
       (Seq (Kleene loop_body)
            (Seq (Assume (Eq (Var "i") (Var "n"))) assert_stmt)))
                 cond_false
                 post_er_bug) =
  let p_init = ISL_Consequence pre_vacia (variant 0) cond_false proof_init () () () in
  let p_loop_assert = ISL_Seq (proof_loop ()) (proof_assert ()) in
  let triple_seq = ISL_Seq p_init p_loop_assert in
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
