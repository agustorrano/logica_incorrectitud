module ListSumLen

open IncSepLogicOne
open FStar.List.Tot
open FStar.Classical

let ( ||| ) = Choice
let enot (e : expr) : expr = Minus (Const 1) e

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

let rec list_seq (i : loc) (j : loc) (xs : list value) (s: state) : Tot prop (decreases xs) =
  match xs with
  | [] -> s._3 == Ok /\ i == j
  | x :: xss ->
    s._3 == Ok /\
    (exists (next_j : loc). (points_to i x ** points_to (i + 1) (Loc next_j) ** list_seq next_j j xss) s)

let rec ones (n : nat) : list value =
  if n = 0 then [] else Nat 1 :: ones (n - 1)

let n_target = 10

let variant (k : nat) : cond = 
  fun (st, hp, m) -> 
    k <= n_target /\ m == Ok /\
    st "sum" == Nat k /\ st "len" == Nat k /\
    (exists (p : loc). st "ptr" == Loc p /\ list_seq p 0 (ones (n_target - k)) (st, hp, m))

let pre_load_v (k : nat) : cond = 
  fun s -> variant k s /\ eval_expr s (enot (Eq (Var "ptr") (Const 0))) == 0

let mid_v (k : nat) : cond =
  fun (st, hp, m) ->
    k < n_target /\ m == Ok /\
    st "sum" == Nat k /\ st "len" == Nat k /\ st "v" == Nat 1 /\
    (exists (p : loc) (next_p : loc). st "ptr" == Loc p /\
      (points_to p (Nat 1) ** points_to (p + 1) (Loc next_p) ** list_seq next_p 0 (ones (n_target - k - 1))) (st, hp, m))

let mid_sum (k : nat) : cond =
  fun (st, hp, m) ->
    k < n_target /\ m == Ok /\
    st "sum" == Nat (k + 1) /\ st "len" == Nat k /\ st "v" == Nat 1 /\
    (exists (p : loc) (next_p : loc). st "ptr" == Loc p /\
      (points_to p (Nat 1) ** points_to (p + 1) (Loc next_p) ** list_seq next_p 0 (ones (n_target - k - 1))) (st, hp, m))

let mid_len (k : nat) : cond =
  fun (st, hp, m) ->
    k < n_target /\ m == Ok /\
    st "sum" == Nat (k + 1) /\ st "len" == Nat (k + 1) /\ st "v" == Nat 1 /\
    (exists (p : loc) (next_p : loc). st "ptr" == Loc p /\
      (points_to p (Nat 1) ** points_to (p + 1) (Loc next_p) ** list_seq next_p 0 (ones (n_target - k - 1))) (st, hp, m))

let pre_vacia : cond = 
  fun s -> s._3 == Ok /\ (exists p. s._1 "ptr" == Loc p /\ list_seq p 0 (ones n_target) s)

let mid_init : cond = 
  fun s -> pre_vacia s /\ s._1 "sum" == Nat 0

let proof_init : isl_triple pre_vacia init_vars (kleene_pre variant) =
  let p_sum_raw = ISL_Assign #pre_vacia "sum" (Const 0) in
  let p_sum = ISL_Consequence pre_vacia mid_init p_sum_raw () () in
  
  let p_len_raw = ISL_Assign #(fun s -> s._3 == Ok /\ mid_init s) "len" (Const 0) in
  let p_len : isl_triple (fun s -> s._3 == Ok /\ mid_init s) (Assign "len" (Const 0)) (kleene_pre variant) = 
    ISL_Consequence (fun s -> s._3 == Ok /\ mid_init s) (kleene_pre variant) p_len_raw () () 
  in
  
  let p_seq = ISL_Seq p_sum p_len in
  ISL_Consequence pre_vacia (kleene_pre variant) p_seq () ()