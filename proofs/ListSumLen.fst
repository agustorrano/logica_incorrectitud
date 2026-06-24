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
    s._3 == Ok /\ 
    (exists (curr_ptr : loc). 
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

let proof_init (start_ptr: loc) : isl_triple (pre_vacia start_ptr) init_vars (kleene_pre (variant start_ptr)) =
  let pre = pre_vacia start_ptr in
  let mid = mid_sum start_ptr in 
  let post = kleene_pre (variant start_ptr) in
  
  let p_sum_raw = ISL_Assign #pre "sum" (Const 0) in
  let p_sum = ISL_Consequence pre mid p_sum_raw () () in
  
  let p_len_raw = ISL_Assign #(fun s -> s._3 == Ok /\ mid s) "len" (Const 0) in
  let p_len : isl_triple (fun s -> s._3 == Ok /\ mid s) (Assign "len" (Const 0)) post = 
    ISL_Consequence (fun s -> s._3 == Ok /\ mid s) post p_len_raw () () 
  in
  
  let p_seq = ISL_Seq p_sum p_len in
  ISL_Consequence pre post p_seq () ()

let lemma_sep_indep (p q : cond) (st1 st2 : store) (hp : heap) (m1 m2 : term_mode)
  : Lemma (requires (forall h. p (st1, h, m1) <==> p (st2, h, m2)) /\
                    (forall h. q (st1, h, m1) <==> q (st2, h, m2)))
          (ensures (p ** q) (st1, hp, m1) <==> (p ** q) (st2, hp, m2)) = ()

let rec lemma_list_seq_indep (i j : loc) (xs : list value) (st1 st2 : store) (hp : heap) (m1 m2 : term_mode)
  : Lemma (ensures list_seq i j xs (st1, hp, m1) <==> list_seq i j xs (st2, hp, m2))
          (decreases xs) =
  match xs with
  | [] -> ()
  | x :: xss ->
    let prove_rec (next_j : loc) (h : heap)
      : Lemma (list_seq next_j j xss (st1, h, m1) <==> list_seq next_j j xss (st2, h, m2)) =
      lemma_list_seq_indep next_j j xss st1 st2 h m1 m2
    in
    let prove_rec_h (next_j : loc)
      : Lemma (forall (h : heap). list_seq next_j j xss (st1, h, m1) <==> list_seq next_j j xss (st2, h, m2)) =
      Classical.forall_intro (prove_rec next_j)
    in
    Classical.forall_intro prove_rec_h;
    
    let p_A = points_to i x in
    let p_B (next_j : loc) = points_to (i + 1) (Loc next_j) in
    let p_C (next_j : loc) = list_seq next_j j xss in
    let p_AB (next_j : loc) : cond = p_A ** p_B next_j in
    let p_body (next_j : loc) : cond = fun s -> (p_AB next_j ** p_C next_j) s in

    let prove_body (next_j : loc)
      : Lemma (p_body next_j (st1, hp, m1) <==> p_body next_j (st2, hp, m2)) =
      let prove_C (h : heap) : Lemma (p_C next_j (st1, h, m1) <==> p_C next_j (st2, h, m2)) =
        lemma_list_seq_indep next_j j xss st1 st2 h m1 m2
      in
      Classical.forall_intro prove_C;

      let prove_AB (h : heap) : Lemma (p_AB next_j (st1, h, m1) <==> p_AB next_j (st2, h, m2)) =
        lemma_sep_indep p_A (p_B next_j) st1 st2 h m1 m2
      in
      Classical.forall_intro prove_AB;
      lemma_sep_indep (p_AB next_j) (p_C next_j) st1 st2 hp m1 m2
    in

    Classical.forall_intro prove_body

let p_fr_mem (start_ptr : loc) (k : nat) (curr_ptr : loc) (next_j : loc) : cond =
  fun s ->
    let xs = ones n_target in
    let l_visit, l_remain = splitAt k xs in
    match l_remain with
    | [] -> False
    | _ :: tl ->
      (points_to (curr_ptr + 1) (Loc next_j) ** 
       list_seq start_ptr curr_ptr l_visit ** 
       list_seq next_j 0 tl) s

let fr_load (start_ptr : loc) (k : nat) : cond =
  fun s ->
    k < n_target /\ s._1 "sum" == Nat k /\ s._1 "len" == Nat k /\
    (exists (curr_ptr next_j: loc).
      s._1 "ptr" == Loc curr_ptr /\
      p_fr_mem start_ptr k curr_ptr next_j s)

let lemma_fr_mem_indep (start_ptr : loc) (k : nat) (curr_ptr : loc) (next_j : loc) (st1 st2 : store) (hp : heap) (m1 m2 : term_mode)
  : Lemma (p_fr_mem start_ptr k curr_ptr next_j (st1, hp, m1) <==> p_fr_mem start_ptr k curr_ptr next_j (st2, hp, m2)) =
  let xs = ones n_target in
  let l_visit, l_remain = splitAt k xs in
  match l_remain with
  | [] -> ()
  | _ :: tl ->
    let p_A = points_to (curr_ptr + 1) (Loc next_j) in
    let p_B = list_seq start_ptr curr_ptr l_visit in
    let p_C = list_seq next_j 0 tl in
    let p_AB : cond = p_A ** p_B in

    let prove_A (h : heap) : Lemma (p_A (st1, h, m1) <==> p_A (st2, h, m2)) = () in
    Classical.forall_intro prove_A;

    let prove_B (h : heap) : Lemma (p_B (st1, h, m1) <==> p_B (st2, h, m2)) =
      lemma_list_seq_indep start_ptr curr_ptr l_visit st1 st2 h m1 m2
    in
    Classical.forall_intro prove_B;

    let prove_C (h : heap) : Lemma (p_C (st1, h, m1) <==> p_C (st2, h, m2)) =
      lemma_list_seq_indep next_j 0 tl st1 st2 h m1 m2
    in
    Classical.forall_intro prove_C;

    let prove_AB (h : heap) : Lemma (p_AB (st1, h, m1) <==> p_AB (st2, h, m2)) =
      lemma_sep_indep p_A p_B st1 st2 h m1 m2
    in
    Classical.forall_intro prove_AB;
    lemma_sep_indep p_AB p_C st1 st2 hp m1 m2

let pf_indep_load (start_ptr : loc) (k : nat)
  : squash (independent_on_vars (modifies (Load "v" (Var "ptr"))) (fr_load start_ptr k)) =

  let prove_indep (st1 st2 : store) (hp : heap) (m1 m2 : term_mode)
    : Lemma (requires match_except_vars (modifies (Load "v" (Var "ptr"))) st1 st2)
            (ensures fr_load start_ptr k (st1, hp, m1) <==> fr_load start_ptr k (st2, hp, m2)) =

    let prove_mem (curr_ptr : loc) (next_j : loc)
      : Lemma (p_fr_mem start_ptr k curr_ptr next_j (st1, hp, m1) <==> p_fr_mem start_ptr k curr_ptr next_j (st2, hp, m2)) =
      lemma_fr_mem_indep start_ptr k curr_ptr next_j st1 st2 hp m1 m2
    in

    Classical.forall_intro (fun c -> Classical.forall_intro (prove_mem c))
  in

  let prove_indep_impl (st1 st2 : store) (hp : heap) (m1 m2 : term_mode)
    : Lemma (match_except_vars (modifies (Load "v" (Var "ptr"))) st1 st2 ==>
            (fr_load start_ptr k (st1, hp, m1) <==> fr_load start_ptr k (st2, hp, m2))) =
    Classical.move_requires (prove_indep st1 st2 hp m1) m2
  in
  
  Classical.forall_intro (fun st1 ->
    Classical.forall_intro (fun st2 ->
      Classical.forall_intro (fun hp ->
        Classical.forall_intro (fun m1 ->
          Classical.forall_intro (fun m2 -> prove_indep_impl st1 st2 hp m1 m2)))))

let pre_loop (start_ptr : loc) (k : nat) (s : state) : prop =
  variant start_ptr k s /\ s._3 == Ok

let mid_assume (start_ptr : loc) (k : nat) (s : state) : prop =
  s._3 == Ok /\ pre_loop start_ptr k s /\
  eval_expr s (enot (Eq (Var "ptr") (Const 0))) == 0

let mid_load_v (start_ptr : loc) (k : nat) : cond =
  fun s -> let xs = ones n_target in
    k < n_target /\ s._3 == Ok /\
    s._1 "v" == Nat 1 /\
    s._1 "sum" == Nat k /\ s._1 "len" == Nat k /\
    (exists (curr_ptr next_j : loc).
      s._1 "ptr" == Loc curr_ptr /\
      (let l_visit, l_remain = splitAt k xs in
      match l_remain with
      | [] -> (fun _ -> False)
      | _ :: tl ->
        (points_to curr_ptr (Nat 1) ** points_to (curr_ptr + 1) (Loc next_j) **
        list_seq start_ptr curr_ptr l_visit ** list_seq next_j 0 tl)) s)

let mid_load_v_ext (start_ptr : loc) (k : nat) (s : state) : prop =
  mid_load_v start_ptr k s /\ eval_expr s (enot (Eq (Var "ptr") (Const 0))) == 0

let proof_step1_assume (start_ptr : loc) (k : nat)
  : isl_triple (pre_loop start_ptr k) 
               (Assume (enot (Eq (Var "ptr") (Const 0)))) 
               (mid_assume start_ptr k) =
  ISL_Assume #(pre_loop start_ptr k) (enot (Eq (Var "ptr") (Const 0)))

let proof_step2_load_v (start_ptr : loc) (k : nat)
  : isl_triple (mid_assume start_ptr k) 
               (Load "v" (Var "ptr")) 
               (mid_load_v_ext start_ptr k) =

  let stmt_load = Load "v" (Var "ptr") in

  let pre_load_v (s : state) : prop = 
    s._3 == Ok /\ (exists (p : loc). s._1 "ptr" == Loc p /\ points_to p (Nat 1) s) /\
    eval_expr s (enot (Eq (Var "ptr") (Const 0))) == 0
  in
    
  let p_load_base = ISL_Load #pre_load_v "v" (Var "ptr") in

  let post_load_base (s : state) : prop =
    exists l v x_old. s._3 == Ok /\ eval_expr (override s._1 "v" x_old, s._2, Ok) (Var "ptr") == l /\
      points_to l v s /\ s._1 "v" == v /\ pre_load_v (override s._1 "v" x_old, s._2, Ok)
  in
  
  let p_load_framed = ISL_Frame #pre_load_v #stmt_load #post_load_base (fr_load start_ptr k) p_load_base (pf_indep_load start_ptr k) in
  
  let pf_load_pre (s : state)
    : Lemma (requires (pre_load_v ** fr_load start_ptr k) s) 
            (ensures mid_assume start_ptr k s) = 
    admit()
  in
  
  let pf_load_post (s : state)
    : Lemma (requires mid_load_v_ext start_ptr k s) 
            (ensures (post_load_base ** fr_load start_ptr k) s) = 
    admit()
  in
  
  let sq_pre_load () : squash (forall x. (pre_load_v ** fr_load start_ptr k) x ==> mid_assume start_ptr k x) =
    Classical.forall_intro (Classical.move_requires pf_load_pre)
  in
  
  let sq_post_load () : squash (forall x. mid_load_v_ext start_ptr k x ==> (post_load_base ** fr_load start_ptr k) x) =
    Classical.forall_intro (Classical.move_requires pf_load_post)
  in
  
  ISL_Consequence #(pre_load_v ** fr_load start_ptr k) #stmt_load #(post_load_base ** fr_load start_ptr k) 
                  (mid_assume start_ptr k) (mid_load_v_ext start_ptr k) 
                  p_load_framed (sq_pre_load ()) (sq_post_load ())