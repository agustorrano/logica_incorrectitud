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

let rec list_seq (i j : loc) (xs : list value) : Tot cond (decreases xs) =
  match xs with
  | [] -> (fun s -> emp s /\ i == j)
  | x :: xss -> (fun s ->
    exists (next_j : loc). 
      (points_to i x ** points_to (i + 1) (Loc next_j) ** list_seq next_j j xss) s)

let rec ones (n : nat) : list value =
  if n = 0 then [] else Nat 1 :: ones (n - 1)

let n_target = 10

let pre_vacia (start_ptr : loc) : cond = 
  fun s -> let xs = ones n_target in
    (exists (curr_ptr : loc). 
      s._3 == Ok /\
      s._1 "ptr" == Loc curr_ptr /\ 
      (let l_visit, l_remain = splitAt 0 xs in
      (list_seq start_ptr curr_ptr l_visit ** list_seq curr_ptr 0 l_remain)) s)

let variant (start_ptr : loc) (k : nat) : cond = 
  fun s ->
    let xs = ones n_target in 
    k <= n_target /\ s._3 == Ok /\
    s._1 "sum" == Nat k /\ s._1 "len" == Nat k /\
    (exists (curr_ptr : loc). 
      s._1 "ptr" == Loc curr_ptr /\ 
      (let l_visit, l_remain = splitAt k xs in
      (list_seq start_ptr curr_ptr l_visit ** list_seq curr_ptr 0 l_remain)) s)

let mid_sum (start_ptr : loc) : cond = 
  fun s -> pre_vacia start_ptr s /\ s._1 "sum" == Nat 0

let proof_init (start_ptr: loc) : isl_triple (is_ok (pre_vacia start_ptr)) init_vars (kleene_pre (variant start_ptr)) =
  let pre = pre_vacia start_ptr in
  let mid = mid_sum start_ptr in 
  let post = kleene_pre (variant start_ptr) in
  
  let p_sum_raw = ISL_Assign #pre "sum" (Const 0) in
  let p_sum = ISL_Consequence pre mid p_sum_raw () () in
  
  let p_len_raw = ISL_Assign #mid "len" (Const 0) in
  let p_len = ISL_Consequence mid post p_len_raw () () in
  
  let p_seq = ISL_Seq p_sum p_len in
  ISL_Consequence pre post p_seq () ()
