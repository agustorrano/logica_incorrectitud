module ListSumLen

open IncSepLogicOne
open FStar.List.Tot
open FStar.Classical

// Utils
let ( ||| ) = Choice
let enot (e : expr) : expr = Minus (Const 1) e

// Definición del programa
let init_vars = 
  Assign "sum" (Const 0) `Seq`
  Assign "len" (Const 0)

let loop_body =
  Assume (enot (Eq (Var "ptr") (Const 0))) `Seq`
  (Load "v" (Var "ptr") `Seq`
  (Assign "sum" (Plus (Var "sum") (Var "v")) `Seq`
  (Assign "len" (Plus (Var "len") (Const 1)) `Seq`
  Load "ptr" (Plus (Var "ptr") (Const 1)))))

let assert_stmt =
  Seq (Assume (Eq (Var "sum") (Var "len"))) Error |||
  Assume (enot (Eq (Var "sum") (Var "len")))

let prog_list_sum_len =
  (Seq init_vars
       (Seq (Kleene loop_body)
            (Seq (Assume (Eq (Var "ptr") (Const 0))) assert_stmt)))

// Lista
let rec list_seg (i j : loc) (xs : list value) : Tot cond (decreases xs) =
  match xs with
  | [] -> (fun s -> emp s /\ i == j)
  | x :: xss -> (fun s ->
    exists (next_j : loc). 
      (points_to i x ** points_to (i + 1) (Loc next_j) ** list_seg next_j j xss) s)

let rec ones (n : nat) : list value =
  if n = 0 then [] else Nat 1 :: ones (n - 1)

let n_target = 10

let rec prefix_seg (start_ptr curr_ptr : loc) (k : nat) : Tot cond (decreases k) =
  if k = 0 then
    fun s -> emp s /\ curr_ptr == start_ptr
  else
    fun s -> exists (prev_ptr : loc).
      (prefix_seg start_ptr prev_ptr (k - 1) **
      points_to prev_ptr (Nat 1) **
      points_to (prev_ptr + 1) (Loc curr_ptr)) s

// Estados intermedios
let pre_init (start_ptr : loc) : cond = 
  fun s -> let xs = ones n_target in
    (exists (curr_ptr : loc). 
      s._3 == Ok /\
      s._1 "ptr" == Loc curr_ptr /\ 
      (prefix_seg start_ptr curr_ptr 0 ** list_seg curr_ptr 0 xs) s)

let post_len_shape (start_ptr curr_ptr next_ptr : loc) (k : nat) : cond =
  fun s ->
    k < n_target /\ s._3 == Ok /\
    s._1 "sum" == Nat (k + 1) /\ s._1 "len" == Nat (k + 1) /\ s._1 "v" == Nat 1 /\
    s._1 "ptr" == Loc curr_ptr /\
    points_to curr_ptr (Nat 1) s /\
    (prefix_seg start_ptr curr_ptr k **
    points_to (curr_ptr + 1) (Loc next_ptr) **
    list_seg next_ptr 0 (ones (n_target - k - 1))) s

let post_ptr_shape (start_ptr : loc) (k : nat) : cond =
  fun s ->
    k == 0 \/
    exists (curr_ptr : loc) (prev_ptr : loc).
      s._1 "ptr" == Loc curr_ptr /\
      points_to (prev_ptr + 1) (Loc curr_ptr) s /\
      post_len_shape start_ptr prev_ptr curr_ptr (k - 1)
        (override s._1 "ptr" (Loc prev_ptr), s._2, Ok)

let variant (start_ptr : loc) (k : nat) : cond = 
  fun s ->
    let xs = ones n_target in 
    k <= n_target /\ s._3 == Ok /\
    s._1 "sum" == Nat k /\ s._1 "len" == Nat k /\
    post_ptr_shape start_ptr k s /\
    (exists (curr_ptr : loc). 
      s._1 "ptr" == Loc curr_ptr /\ 
      (prefix_seg start_ptr curr_ptr k ** list_seg curr_ptr 0 (ones (n_target - k))) s)

let mid_sum (start_ptr : loc) : cond = 
  fun s -> pre_init start_ptr s /\ s._1 "sum" == Nat 0

let mid_assume (start_ptr : loc) (k : nat) : cond =
  fun s -> variant start_ptr k s /\ eval_expr s (enot (Eq (Var "ptr") (Const 0))) == 0

let post_load_v (start_ptr : loc) (k : nat) : cond =
  fun s ->
    let xs = ones n_target in
    k < n_target /\ s._3 == Ok /\
    s._1 "sum" == Nat k /\ s._1 "len" == Nat k /\ s._1 "v" == Nat 1 /\
    (exists (curr_ptr : loc) (next_ptr : loc).
      s._1 "ptr" == Loc curr_ptr /\
      points_to curr_ptr (Nat 1) s /\
      (prefix_seg start_ptr curr_ptr k **
      points_to (curr_ptr + 1) (Loc next_ptr) **
      list_seg next_ptr 0 (ones (n_target - k - 1))) s)

let post_sum (start_ptr : loc) (k : nat) : cond =
  fun s ->
    let xs = ones n_target in
    k < n_target /\ s._3 == Ok /\
    s._1 "sum" == Nat (k + 1) /\ s._1 "len" == Nat k /\ s._1 "v" == Nat 1 /\
    (exists (curr_ptr : loc) (next_ptr : loc).
      s._1 "ptr" == Loc curr_ptr /\
      points_to curr_ptr (Nat 1) s /\
      (prefix_seg start_ptr curr_ptr k **
      points_to (curr_ptr + 1) (Loc next_ptr) **
      list_seg next_ptr 0 (ones (n_target - k - 1))) s)

let post_len (start_ptr : loc) (k : nat) : cond =
  fun s ->
    k < n_target /\ s._3 == Ok /\
    s._1 "sum" == Nat (k + 1) /\ s._1 "len" == Nat (k + 1) /\ s._1 "v" == Nat 1 /\
    (exists (curr_ptr : loc) (next_ptr : loc).
      s._1 "ptr" == Loc curr_ptr /\
      points_to curr_ptr (Nat 1) s /\
      (prefix_seg start_ptr curr_ptr k **
      points_to (curr_ptr + 1) (Loc next_ptr) **
      list_seg next_ptr 0 (ones (n_target - k - 1))) s)

let pre_assert (start_ptr : loc) : cond =
  fun s -> exists (k : nat). variant start_ptr k s

let pre_error (start_ptr : loc) : cond =
  fun s -> variant start_ptr n_target s /\ s._1 "ptr" == Loc 0 /\
           eval_expr s (Eq (Var "sum") (Var "len")) == 0

let post_error (start_ptr : loc) : cond =
  fun s -> s._3 == Er /\ pre_error start_ptr (s._1, s._2, Ok)

// Lemas auxiliares
let lemma_prove_load_v (start_ptr : loc) (k : nat) (s : state)
  : Lemma (requires (post_load_v start_ptr k s))
          (ensures (is_ok (fun s0 -> exists (l : loc) (v : value) (x_old : value).
                    eval_expr (override s0._1 "v" x_old, s0._2, Ok) (Var "ptr") == l /\
                    points_to l v s0 /\
                    s0._1 "v" == v /\
                    (mid_assume start_ptr k) (override s0._1 "v" x_old, s0._2, Ok)) s)) =
  let st, hp, m = s in
  let curr_ptr =
    FStar.IndefiniteDescription.indefinite_description_ghost loc
      (fun curr_ptr ->
        exists next_ptr.
          s._1 "ptr" == Loc curr_ptr /\
          points_to curr_ptr (Nat 1) s /\
          (prefix_seg start_ptr curr_ptr k **
          points_to (curr_ptr + 1) (Loc next_ptr) **
          list_seg next_ptr 0 (ones (n_target - k - 1))) s)
  in
  let x_old = st "v" in
  let l = curr_ptr in
  let v = Nat 1 in
  let s0 = (override st "v" x_old, hp, Ok) in
  assert (variant start_ptr k s0);
  Classical.exists_intro (fun l -> exists (v : value) (x_old : value).
    eval_expr (override s._1 "v" x_old, s._2, Ok) (Var "ptr") == l /\
    points_to l v s /\
    s._1 "v" == v /\
    (mid_assume start_ptr k) (override s._1 "v" x_old, s._2, Ok)) l;
  Classical.exists_intro (fun v -> exists (x_old : value).
    eval_expr (override s._1 "v" x_old, s._2, Ok) (Var "ptr") == l /\
    points_to l v s /\
    s._1 "v" == v /\
    (mid_assume start_ptr k) (override s._1 "v" x_old, s._2, Ok)) v;
  Classical.exists_intro (fun x_old ->
    eval_expr (override s._1 "v" x_old, s._2, Ok) (Var "ptr") == l /\
    points_to l v s /\
    s._1 "v" == v /\
    (mid_assume start_ptr k) (override s._1 "v" x_old, s._2, Ok)) x_old

let lemma_prove_sum_step (start_ptr : loc) (k : nat) (s : state)
  : Lemma (requires (post_sum start_ptr k s))
          (ensures (is_ok (fun s0 -> exists (st_init : var -> value).
                    post_load_v start_ptr k (st_init, s0._2, s0._3) /\
                    s._1 "sum" == Nat (eval_expr (st_init, s0._2, s0._3) (Plus (Var "sum") (Var "v"))) /\
                    (forall (y : var). y <> "sum" ==> s._1 y == st_init y)) s)) =
  let st, hp, m = s in
  let st_init = override st "sum" (Nat k) in
  let p_exist (st_i : var -> value) : prop =
    post_load_v start_ptr k (st_i, hp, m) /\
    st "sum" == Nat (eval_expr (st_i, hp, m) (Plus (Var "sum") (Var "v"))) /\
    (forall (y : var). y <> "sum" ==> st y == st_i y)
  in
  Classical.exists_intro p_exist st_init

let lemma_prove_len_step (start_ptr : loc) (k : nat) (s : state)
  : Lemma (requires (post_len start_ptr k s))
          (ensures (is_ok (fun s0 -> exists (st_init : var -> value).
                    post_sum start_ptr k (st_init, s0._2, s0._3) /\
                    s._1 "len" == Nat (eval_expr (st_init, s0._2, s0._3) (Plus (Var "len") (Const 1))) /\
                    (forall (y : var). y <> "len" ==> s._1 y == st_init y)) s)) =
  let st, hp, m = s in
  let st_init = override st "len" (Nat k) in
  let p_exist (st_i : var -> value) : prop =
    post_sum start_ptr k (st_i, hp, m) /\
    st "len" == Nat (eval_expr (st_i, hp, m) (Plus (Var "len") (Const 1))) /\
    (forall (y : var). y <> "len" ==> st y == st_i y)
  in
  Classical.exists_intro p_exist st_init

let lemma_prove_load_ptr (start_ptr : loc) (k : nat) (s : state)
  : Lemma (requires (variant start_ptr (k + 1) s))
          (ensures (is_ok (fun s0 -> exists (l : loc) (v : value) (x_old : value).
                    eval_expr (override s0._1 "ptr" x_old, s0._2, Ok) (Plus (Var "ptr") (Const 1)) == l /\
                    points_to l v s0 /\
                    s0._1 "ptr" == v /\
                    post_len start_ptr k (override s0._1 "ptr" x_old, s0._2, Ok)) s)) =
  let st, hp, m = s in
  let old_ptr = FStar.IndefiniteDescription.indefinite_description_ghost loc
    (fun old_ptr -> exists next_ptr.
      st "ptr" == Loc next_ptr /\
      points_to (old_ptr + 1) (Loc next_ptr) s /\
      post_len_shape start_ptr old_ptr next_ptr k
        (override st "ptr" (Loc old_ptr), hp, Ok))
  in
  let next_ptr = FStar.IndefiniteDescription.indefinite_description_ghost loc
    (fun next_ptr ->
      st "ptr" == Loc next_ptr /\
      points_to (old_ptr + 1) (Loc next_ptr) s /\
      post_len_shape start_ptr old_ptr next_ptr k
        (override st "ptr" (Loc old_ptr), hp, Ok))
  in
  let l = old_ptr + 1 in
  let v = Loc next_ptr in
  let x_old = Loc old_ptr in
  let p_exist (l0 : loc) : prop = exists (v0 : value) (x0 : value).
    eval_expr (override st "ptr" x0, hp, Ok) (Plus (Var "ptr") (Const 1)) == l0 /\
    points_to l0 v0 s /\
    st "ptr" == v0 /\
    post_len start_ptr k (override st "ptr" x0, hp, Ok)
  in
  Classical.exists_intro p_exist l;
  Classical.exists_intro (fun v0 -> exists (x0 : value).
    eval_expr (override st "ptr" x0, hp, Ok) (Plus (Var "ptr") (Const 1)) == l /\
    points_to l v0 s /\
    st "ptr" == v0 /\
    post_len start_ptr k (override st "ptr" x0, hp, Ok)) v;
  Classical.exists_intro (fun x0 ->
    eval_expr (override st "ptr" x0, hp, Ok) (Plus (Var "ptr") (Const 1)) == l /\
    points_to l v s /\
    st "ptr" == v /\
    post_len start_ptr k (override st "ptr" x0, hp, Ok)) x_old

let lemma_empty_lseg (n : nat) (s : state)
  : Lemma (requires (list_seg 0 0 (ones n) s))
          (ensures n == 0) =
  match n with
  | 0 -> ()
  | _ -> ()

let lemma_exit_target (start_ptr : loc) (s : state)
  : Lemma (requires (pre_assert start_ptr s /\ eval_expr s (Eq (Var "ptr") (Const 0)) == 0))
          (ensures (pre_error start_ptr s)) =
  let k = FStar.IndefiniteDescription.indefinite_description_ghost nat
    (fun k -> variant start_ptr k s)
  in
  let curr_ptr = FStar.IndefiniteDescription.indefinite_description_ghost loc
    (fun curr_ptr ->
      s._1 "ptr" == Loc curr_ptr /\
      (prefix_seg start_ptr curr_ptr k ** list_seg curr_ptr 0 (ones (n_target - k))) s)
  in
  let h_tail = FStar.IndefiniteDescription.indefinite_description_ghost heap
    (fun h_tail -> list_seg curr_ptr 0 (ones (n_target - k)) (s._1, h_tail, s._3))
  in
  lemma_empty_lseg (n_target - k) (s._1, h_tail, s._3)

// Demostraciones
let proof_init (start_ptr: loc) : isl_triple (is_ok (pre_init start_ptr)) init_vars (kleene_pre (variant start_ptr)) =
  let pre = pre_init start_ptr in
  let mid = mid_sum start_ptr in 
  let post = kleene_pre (variant start_ptr) in
  
  let p_sum_raw = ISL_Assign #pre "sum" (Const 0) in
  let p_sum = ISL_Consequence pre mid p_sum_raw () () in
  
  let p_len_raw = ISL_Assign #mid "len" (Const 0) in
  let p_len = ISL_Consequence mid post p_len_raw () () in
  
  let p_seq = ISL_Seq p_sum p_len in
  ISL_Consequence pre post p_seq () ()

let proof_loop_step (start_ptr : loc) (k : nat)
  : isl_triple (is_ok (variant start_ptr k)) loop_body (variant start_ptr (k + 1)) =
  let pre_assume s = variant start_ptr k s /\ eval_expr s (enot (Eq (Var "ptr") (Const 0))) == 0 in
  let p_assumed = ISL_Assume #(variant start_ptr k) (enot (Eq (Var "ptr") (Const 0))) in

  let p_load_v_raw = ISL_Load #(mid_assume start_ptr k) "v" (Var "ptr") in
  let pf_load = Classical.forall_intro (Classical.move_requires (lemma_prove_load_v start_ptr k)) in
  let p_load_v = ISL_Consequence (mid_assume start_ptr k) (post_load_v start_ptr k) p_load_v_raw () pf_load in

  let p_sum_raw = ISL_Assign #(post_load_v start_ptr k) "sum" (Plus (Var "sum") (Var "v")) in
  let pf_sum = Classical.forall_intro (Classical.move_requires (lemma_prove_sum_step start_ptr k)) in
  let p_sum = ISL_Consequence (post_load_v start_ptr k) (post_sum start_ptr k) p_sum_raw () pf_sum in

  let p_len_raw = ISL_Assign #(post_sum start_ptr k) "len" (Plus (Var "len") (Const 1)) in
  let pf_len = Classical.forall_intro (Classical.move_requires (lemma_prove_len_step start_ptr k)) in
  let p_len = ISL_Consequence (post_sum start_ptr k) (post_len start_ptr k) p_len_raw () pf_len in

  let p_ptr_raw = ISL_Load #(post_len start_ptr k) "ptr" (Plus (Var "ptr") (Const 1)) in
  let pf_ptr = Classical.forall_intro (Classical.move_requires (lemma_prove_load_ptr start_ptr k)) in
  let p_ptr = ISL_Consequence (post_len start_ptr k) (variant start_ptr (k + 1)) p_ptr_raw () pf_ptr in

  let p_seq1 = ISL_Seq p_len p_ptr in
  let p_seq2 = ISL_Seq p_sum p_seq1 in
  let p_seq3 = ISL_Seq p_load_v p_seq2 in
  let expected_post_seq3 : cond = fun s -> variant start_ptr (k + 1) s \/ (s._3 == Er /\ post_len start_ptr k s) in

  let p_seq3_adapted = ISL_Consequence #(mid_assume start_ptr k) (is_ok (mid_assume start_ptr k)) expected_post_seq3 p_seq3 () () in

  let p_raw = ISL_Seq p_assumed p_seq3_adapted in
  ISL_Consequence (variant start_ptr k) (variant start_ptr (k + 1)) p_raw () ()

let lemma_kleene  (start_ptr : loc) : isl_triple (kleene_pre (variant start_ptr)) (Kleene loop_body) (kleene_post (variant start_ptr)) =
  let step (n : nat) =
    ISL_Consequence
      (variant start_ptr n)
      (variant start_ptr (n + 1))
      (proof_loop_step start_ptr n)
      () ()
  in
  ISL_KleeneVariant #(variant start_ptr) #loop_body step

let proof_assert (start_ptr : loc)
  : isl_triple (is_ok (pre_assert start_ptr))
    (Seq (Assume (Eq (Var "ptr") (Const 0))) assert_stmt)
    (post_error start_ptr) =
  let p_exit_raw = ISL_Assume #(pre_assert start_ptr) (Eq (Var "ptr") (Const 0)) in
  let pf_exit = Classical.forall_intro (Classical.move_requires (lemma_exit_target start_ptr)) in
  let p_exit = ISL_Consequence (pre_assert start_ptr) (pre_error start_ptr) p_exit_raw () pf_exit in

  let p_cond_err_raw = ISL_Assume #(pre_error start_ptr) (Eq (Var "sum") (Var "len")) in
  let p_cond_err = ISL_Consequence (pre_error start_ptr) (pre_error start_ptr) p_cond_err_raw () () in
  let p_err_raw = ISL_Error #(pre_error start_ptr) in

  let p_branch_err_raw = ISL_Seq p_cond_err p_err_raw in
  let p_branch_err = ISL_Consequence (pre_error start_ptr) (post_error start_ptr) p_branch_err_raw () () in

  let p_assert = ISL_ChoiceL p_branch_err in
  let p_raw = ISL_Seq p_exit p_assert in
  ISL_Consequence (pre_assert start_ptr) (post_error start_ptr) p_raw () ()

let proof_prog_list_sum_len (start_ptr : loc)
  : isl_triple (is_ok (pre_init start_ptr)) prog_list_sum_len (post_error start_ptr) =
  let adapted_assert = ISL_Consequence (kleene_post (variant start_ptr)) (post_error start_ptr) (proof_assert start_ptr) () () in
  let p_kleene_assert_raw = ISL_Seq (lemma_kleene start_ptr) adapted_assert in
  let p_kleene_assert = ISL_Consequence (kleene_pre (variant start_ptr)) (post_error start_ptr) p_kleene_assert_raw () () in

  let p_raw = ISL_Seq (proof_init start_ptr) p_kleene_assert in
  ISL_Consequence (pre_init start_ptr) (post_error start_ptr) p_raw () ()
