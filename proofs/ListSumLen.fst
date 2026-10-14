module ListSumLen

open IncSepLogic
open FStar.List.Tot
open FStar.Classical
module FE = FStar.FunctionalExtensionality
module ID = FStar.IndefiniteDescription

#push-options "--fuel 8 --ifuel 2 --z3rlimit 100"

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
  Seq init_vars
    (Seq (Kleene loop_body)
      (Seq (Assume (Eq (Var "ptr") (Const 0))) assert_stmt))

// Lista
let rec list_seg (i j : loc) (xs : list value) : Tot cond (decreases xs) =
  match xs with
  | [] -> fun s -> emp s /\ i == j
  | x :: xss -> fun s -> 
    exists (next : loc).
      (points_to i x ** points_to (i + 1) (Loc next) ** list_seg next j xss) s

let rec ones (n : nat) : list value =
  if n = 0 then [] else Nat 1 :: ones (n - 1)

let n_target = 10

// Lectura con marco
let g_old = "list_old"
let g_addr = "list_addr"
let g_value = "list_value"

let ghost_free (pre : cond) : prop =
  forall (st : store) (hp : heap) (m : term_mode) (g : var) (v : value).
    (g == g_old \/ g == g_addr \/ g == g_value) ==>
    (pre (override st g v, hp, m) <==> pre (st, hp, m))

let load_post (pre : cond) (x : var) (e : expr) : cond =
  fun s -> s._3 == Ok /\
    exists (x_old : value) (l : loc) (v : value).
      l <> 0 /\ s._2 l == Full v /\ s._1 x == v /\
      eval_expr (override s._1 x x_old, s._2, Ok) e == l /\
      pre (override s._1 x x_old, s._2, Ok)

let ghost_update (pre : cond) (st : store) (hp : heap) (m : term_mode)
  (g : var) (v : value) (#free : squash (ghost_free pre))
  : Lemma (requires (g == g_old \/ g == g_addr \/ g == g_value))
          (ensures (pre (override st g v, hp, m) <==> pre (st, hp, m))) =
  ()

let ghost_updates (pre : cond) (st : store) (hp : heap) (m : term_mode)
  (wv wa wo : value) (#free : squash (ghost_free pre))
  : Lemma (ensures (pre (override (override (override st g_value wv) g_addr wa) g_old wo, hp, m)
            <==> pre (st, hp, m))) =
  ghost_update pre st hp m g_value wv #();
  ghost_update pre (override st g_value wv) hp m g_addr wa #();
  ghost_update pre (override (override st g_value wv) g_addr wa) hp m g_old wo #()

let split_cell (st : store) (hp : heap) (l : loc) (v : value)
  : Lemma (requires hp l == Full v)
          (ensures heaps_disjoint (singleton_full_heap l v) (heap_without hp l) /\
            hp == heap_union (singleton_full_heap l v) (heap_without hp l)) =
  FE.extensionality loc (fun _ -> cell) hp
    (heap_union (singleton_full_heap l v) (heap_without hp l))

let load_fresh (x : var) (e : expr) : prop =
  x <> g_old /\ x <> g_addr /\ x <> g_value /\
  ~(fv_expr e g_old) /\ ~(fv_expr e g_addr) /\ ~(fv_expr e g_value)

let load_addr (st : store) = eval_expr' st (Var g_addr)

let load_local_pre (x : var) (e : expr) : cond =
  fun s -> s._3 == Ok /\ s._1 x == s._1 g_old /\
    eval_expr s e == load_addr s._1 /\
    points_to (load_addr s._1) (s._1 g_value) s

let load_local_post (x : var) (e : expr) : cond =
  fun s -> s._3 == Ok /\ s._1 x == s._1 g_value /\
    eval_expr (override s._1 x (s._1 g_old), s._2, Ok) e == load_addr s._1 /\
    points_to (load_addr s._1) (s._1 g_value) s

let load_frame (pre : cond) (x : var) : cond =
  fun s -> s._2 (load_addr s._1) == Unknown /\
    pre (override s._1 x (s._1 g_old), override s._2 (load_addr s._1) (Full (s._1 g_value)), Ok)

// Lemas de la lectura con marco
let lemma_load_back (x : var) (e : expr)
  (#fresh : squash (load_fresh x e)) (s : state)
  : Lemma (requires load_local_post x e s)
          (ensures exists (l : loc) (v old : value).
            eval_expr (override s._1 x old, s._2, Ok) e == l /\
            points_to l v s /\ s._1 x == v /\
            load_local_pre x e (override s._1 x old, s._2, Ok)) =
  eval_expr_fresh s (Var g_addr) x (s._1 g_old);
  exists_intro (fun old ->
    eval_expr (override s._1 x old, s._2, Ok) e == load_addr s._1 /\
    points_to (load_addr s._1) (s._1 g_value) s /\ s._1 x == s._1 g_value /\
    load_local_pre x e (override s._1 x old, s._2, Ok)) (s._1 g_old);
  exists_intro (fun v -> exists (old : value).
    eval_expr (override s._1 x old, s._2, Ok) e == load_addr s._1 /\
    points_to (load_addr s._1) v s /\ s._1 x == v /\
    load_local_pre x e (override s._1 x old, s._2, Ok)) (s._1 g_value);
  exists_intro (fun l -> exists (v old : value).
    eval_expr (override s._1 x old, s._2, Ok) e == l /\
    points_to l v s /\ s._1 x == v /\
    load_local_pre x e (override s._1 x old, s._2, Ok)) (load_addr s._1)

let lemma_load_frame_independent (pre : cond) (x : var) (e : expr)
  (#fresh : squash (load_fresh x e))
  (st1 st2 : store) (hp : heap) (m1 m2 : term_mode)
  : Lemma (requires match_except_vars (modifies (Load x e)) st1 st2)
          (ensures (load_frame pre x (st1, hp, m1) <==>
            load_frame pre x (st2, hp, m2))) =
  state_equiv_eq (override st1 x (st1 g_old), hp, Ok) (override st2 x (st2 g_old), hp, Ok)

let lemma_load_post_implies (pre : cond) (x : var) (e : expr)
  (#fresh : squash (load_fresh x e)) (#free : squash (ghost_free pre))
  (s : state)
  : Lemma (requires load_post pre x e s)
          (ensures exists_var g_value
            (exists_var g_addr (exists_var g_old
              (load_local_post x e ** load_frame pre x))) s) =
  let old = ID.indefinite_description_ghost
    value (fun old ->
      exists (l : loc) (v : value). l <> 0 /\ s._2 l == Full v /\
        s._1 x == v /\ eval_expr (override s._1 x old, s._2, Ok) e == l /\
        pre (override s._1 x old, s._2, Ok))
  in
  let l = eval_expr (override s._1 x old, s._2, Ok) e in
  let v = s._1 x in
  let st = override (override (override s._1 g_value v) g_addr (Loc l)) g_old old in
  let h1 = singleton_full_heap l v in
  let h2 = heap_without s._2 l in
  split_cell st s._2 l v;
  state_equiv_eq (override s._1 x old, s._2, Ok) (override s._1 x old, override h2 l (Full v), Ok);
  eval_expr_fresh (override s._1 x old, s._2, Ok) e g_value v;
  eval_expr_fresh (override (override s._1 x old) g_value v, s._2, Ok) e g_addr (Loc l);
  eval_expr_fresh (override (override (override s._1 x old) g_value v) g_addr (Loc l), s._2, Ok) e g_old old;
  state_equiv_eq (override st x (st g_old), s._2, Ok)
    (override (override (override (override s._1 x old) g_value v) g_addr (Loc l)) g_old old, s._2, Ok);
  ghost_updates pre (override s._1 x old) s._2 Ok v (Loc l) old #();
  exists_intro (fun a -> exists b.
    heaps_disjoint a b /\ s._2 == heap_union a b /\
    load_local_post x e (st, a, Ok) /\ load_frame pre x (st, b, Ok)) h1;
  exists_intro (fun b -> heaps_disjoint h1 b /\ s._2 == heap_union h1 b /\
    load_local_post x e (st, h1, Ok) /\ load_frame pre x (st, b, Ok)) h2;
  exists_intro (fun w -> (load_local_post x e ** load_frame pre x)
    (override (override (override s._1 g_value v) g_addr (Loc l)) g_old w, s._2, s._3)) old;
  exists_intro (fun w -> exists_var g_old (load_local_post x e ** load_frame pre x)
    (override (override s._1 g_value v) g_addr w, s._2, s._3)) (Loc l);
  exists_intro (fun w -> exists_var g_addr
    (exists_var g_old (load_local_post x e ** load_frame pre x))
    (override s._1 g_value w, s._2, s._3)) v

let lemma_load_pre_implies (pre : cond) (x : var) (e : expr)
  (#free : squash (ghost_free pre)) (s : state)
  : Lemma (requires exists_var g_value
            (exists_var g_addr (exists_var g_old (load_local_pre x e ** load_frame pre x))) s)
          (ensures pre s) =
  let wv = ID.indefinite_description_ghost
    value (fun wv ->
      exists_var g_addr (exists_var g_old (load_local_pre x e ** load_frame pre x)) (override s._1 g_value wv, s._2, s._3))
  in
  let wa = ID.indefinite_description_ghost
    value (fun wa ->
      exists_var g_old (load_local_pre x e ** load_frame pre x) (override (override s._1 g_value wv) g_addr wa, s._2, s._3))
  in
  let wo = ID.indefinite_description_ghost
    value (fun wo ->
      (load_local_pre x e ** load_frame pre x) (override (override (override s._1 g_value wv) g_addr wa) g_old wo, s._2, s._3))
  in
  let st = override (override (override s._1 g_value wv) g_addr wa) g_old wo in
  let h1 = ID.indefinite_description_ghost
    heap (fun h1 -> exists h2.
      heaps_disjoint h1 h2 /\ s._2 == heap_union h1 h2 /\
      load_local_pre x e (st, h1, s._3) /\ load_frame pre x (st, h2, s._3))
  in
  let h2 = ID.indefinite_description_ghost
    heap (fun h2 ->
      heaps_disjoint h1 h2 /\ s._2 == heap_union h1 h2 /\
      load_local_pre x e (st, h1, s._3) /\ load_frame pre x (st, h2, s._3))
  in
  state_equiv_eq (override st x (st g_old), override h2 (load_addr st) (Full (st g_value)), Ok) (st, s._2, Ok);
  ghost_updates pre s._1 s._2 Ok wv wa wo #()

let framed_load (pre : cond) (x : var) (e : expr)
  (#fresh : squash (load_fresh x e)) (#free : squash (ghost_free pre))
  : isl_triple (is_ok pre) (Load x e) (load_post pre x e) =
  let local_pf = ISL_Consequence (load_local_pre x e) (load_local_post x e)
    (ISL_Load #(load_local_pre x e) x e) ()
    (forall_intro (move_requires (lemma_load_back x e #()))) in
  let framed = ISL_Frame (load_frame pre x) local_pf
    (forall_intro (fun st1 -> forall_intro (fun st2 -> forall_intro (fun hp ->
      forall_intro (fun m1 -> forall_intro
        (move_requires (lemma_load_frame_independent pre x e #() st1 st2 hp m1))))))) in
  let hidden = ISL_Exists g_value
    (ISL_Exists g_addr (ISL_Exists g_old framed ()) ()) () in
  ISL_Consequence pre (load_post pre x e) hidden
    (forall_intro (move_requires (lemma_load_pre_implies pre x e #())))
    (forall_intro (move_requires (lemma_load_post_implies pre x e #() #())))

// Estados intermedios
let rec history (start_ptr curr_ptr : loc) (k : nat) (hp : heap)
  : GTot prop (decreases k) =
  if k = 0 then
    curr_ptr == start_ptr /\
    list_seg start_ptr 0 (ones n_target) (FE.on var (fun _ -> Nat 0), hp, Ok)
  else exists (prev_ptr : loc).
    prev_ptr <> 0 /\ hp prev_ptr == Full (Nat 1) /\
    hp (prev_ptr + 1) == Full (Loc curr_ptr) /\
    history start_ptr prev_ptr (k - 1) hp

let pre_init (start_ptr : loc) : cond =
  fun s -> s._3 == Ok /\
    s._1 "ptr" == Loc start_ptr /\
    history start_ptr start_ptr 0 s._2

let variant (start_ptr : loc) (k : nat) : cond =
  fun s ->
    k <= n_target /\ s._3 == Ok /\
    s._1 "sum" == Nat k /\ s._1 "len" == Nat k /\
    (k > 0 ==> s._1 "v" == Nat 1) /\
    exists (curr_ptr : loc).
      s._1 "ptr" == Loc curr_ptr /\
      history start_ptr curr_ptr k s._2

let mid_sum (start_ptr : loc) : cond =
  fun s -> pre_init start_ptr s /\ s._1 "sum" == Nat 0

let mid_assume (start_ptr : loc) (k : nat) : cond =
  fun s -> variant start_ptr k s /\ eval_expr s (enot (Eq (Var "ptr") (Const 0))) <> 0

let post_load_v (start_ptr : loc) (k : nat) : cond =
  fun s ->
    k < n_target /\ mid_assume start_ptr k s /\ s._1 "v" == Nat 1 /\
    exists (curr_ptr : loc). 
      s._1 "ptr" == Loc curr_ptr /\ s._2 curr_ptr == Full (Nat 1)

let post_sum (start_ptr : loc) (k : nat) : cond =
  fun s ->
    k < n_target /\ s._3 == Ok /\
    s._1 "sum" == Nat (k + 1) /\ s._1 "len" == Nat k /\
    s._1 "v" == Nat 1 /\
    exists (curr_ptr : loc).
      curr_ptr <> 0 /\ s._1 "ptr" == Loc curr_ptr /\
      history start_ptr curr_ptr k s._2 /\
      s._2 curr_ptr == Full (Nat 1)

let post_len (start_ptr : loc) (k : nat) : cond =
  fun s ->
    k < n_target /\ s._3 == Ok /\
    s._1 "sum" == Nat (k + 1) /\ s._1 "len" == Nat (k + 1) /\
    s._1 "v" == Nat 1 /\
    exists (curr_ptr : loc).
      curr_ptr <> 0 /\ s._1 "ptr" == Loc curr_ptr /\
      history start_ptr curr_ptr k s._2 /\
      s._2 curr_ptr == Full (Nat 1)

let pre_assert (start_ptr : loc) : cond =
  fun s -> exists (k : nat). variant start_ptr k s

let pre_error (start_ptr : loc) : cond =
  fun s ->
    variant start_ptr n_target s /\ s._1 "ptr" == Loc 0 /\
    eval_expr s (Eq (Var "sum") (Var "len")) <> 0

let post_error (start_ptr : loc) : cond =
  fun s -> s._3 == Er /\ pre_error start_ptr (s._1, s._2, Ok)

// Lemas auxiliares
let lemma_mid_assume_ghost (start_ptr : loc) (k : nat)
  (st : store) (hp : heap) (m : term_mode) (g : var) (v : value)
  : Lemma (requires (g == g_old \/ g == g_addr \/ g == g_value))
          (ensures (mid_assume start_ptr k (override st g v, hp, m) <==>
            mid_assume start_ptr k (st, hp, m))) =
  eval_expr_fresh (st, hp, m) (enot (Eq (Var "ptr") (Const 0))) g v

let lemma_prove_sum_step (start_ptr : loc) (k : nat) (s : state)
  : Lemma (requires (post_sum start_ptr k s))
          (ensures (is_ok (fun s0 -> exists (st_init : store).
            post_load_v start_ptr k (st_init, s0._2, s0._3) /\
            s0._1 "sum" == Nat (eval_expr (st_init, s0._2, s0._3) (Plus (Var "sum") (Var "v"))) /\
            (forall (y : var). y <> "sum" ==> s0._1 y == st_init y)) s)) =
  let st_init = override s._1 "sum" (Nat k) in
  exists_intro (fun (st_init : store) ->
    post_load_v start_ptr k (st_init, s._2, s._3) /\
    s._1 "sum" == Nat (eval_expr (st_init, s._2, s._3) (Plus (Var "sum") (Var "v"))) /\
    (forall (y : var). y <> "sum" ==> s._1 y == st_init y)) st_init

let lemma_prove_len_step (start_ptr : loc) (k : nat) (s : state)
  : Lemma (requires (post_len start_ptr k s))
          (ensures (is_ok (fun s0 -> exists (st_init : store).
            post_sum start_ptr k (st_init, s0._2, s0._3) /\
            s0._1 "len" == Nat (eval_expr (st_init, s0._2, s0._3) (Plus (Var "len") (Const 1))) /\
            (forall (y : var). y <> "len" ==> s0._1 y == st_init y)) s)) =
  let st_init = override s._1 "len" (Nat k) in
  exists_intro (fun (st_init : store) ->
    post_sum start_ptr k (st_init, s._2, s._3) /\
    s._1 "len" == Nat (eval_expr (st_init, s._2, s._3) (Plus (Var "len") (Const 1))) /\
    (forall (y : var). y <> "len" ==> s._1 y == st_init y)) st_init

let lemma_prove_load_v (start_ptr : loc) (k : nat) (s : state)
  : Lemma (requires post_load_v start_ptr k s)
          (ensures load_post (mid_assume start_ptr k) "v" (Var "ptr") s) =
  let curr_ptr = ID.indefinite_description_ghost
    loc (fun curr_ptr -> s._1 "ptr" == Loc curr_ptr /\ s._2 curr_ptr == Full (Nat 1))
  in
  state_equiv_eq (override s._1 "v" (s._1 "v"), s._2, Ok) s;
  exists_intro (fun v ->
    curr_ptr <> 0 /\ s._2 curr_ptr == Full v /\ s._1 "v" == v /\
    eval_expr (override s._1 "v" (s._1 "v"), s._2, Ok) (Var "ptr") == curr_ptr /\
    mid_assume start_ptr k (override s._1 "v" (s._1 "v"), s._2, Ok)) (Nat 1);
  exists_intro (fun l -> exists (v : value).
    l <> 0 /\ s._2 l == Full v /\ s._1 "v" == v /\
    eval_expr (override s._1 "v" (s._1 "v"), s._2, Ok) (Var "ptr") == l /\
    mid_assume start_ptr k (override s._1 "v" (s._1 "v"), s._2, Ok)) curr_ptr;
  exists_intro (fun x_old -> exists (l : loc) (v : value).
    l <> 0 /\ s._2 l == Full v /\ s._1 "v" == v /\
    eval_expr (override s._1 "v" x_old, s._2, Ok) (Var "ptr") == l /\
    mid_assume start_ptr k (override s._1 "v" x_old, s._2, Ok)) (s._1 "v")

let eval_pointer (st : store) (hp : heap) (p : loc)
  : Lemma (ensures eval_expr (override st "ptr" (Loc p), hp, Ok) (Plus (Var "ptr") (Const 1)) == p + 1) =
  assert_norm (eval_expr (override st "ptr" (Loc p), hp, Ok)
    (Plus (Var "ptr") (Const 1)) == p + 1)

let lemma_prove_load_ptr (start_ptr : loc) (k : nat) (s : state)
  : Lemma (requires variant start_ptr (k + 1) s)
          (ensures load_post (post_len start_ptr k) "ptr" (Plus (Var "ptr") (Const 1)) s) =
  let curr_ptr = ID.indefinite_description_ghost
    loc (fun curr_ptr -> s._1 "ptr" == Loc curr_ptr /\ history start_ptr curr_ptr (k + 1) s._2)
  in
  let prev_ptr = ID.indefinite_description_ghost
    loc (fun prev_ptr ->
      prev_ptr <> 0 /\ s._2 prev_ptr == Full (Nat 1) /\
      s._2 (prev_ptr + 1) == Full (Loc curr_ptr) /\
      history start_ptr prev_ptr k s._2)
  in
  exists_intro (fun p ->
    p <> 0 /\ (override s._1 "ptr" (Loc prev_ptr)) "ptr" == Loc p /\
    history start_ptr p k s._2 /\ s._2 p == Full (Nat 1)) prev_ptr;
  eval_pointer s._1 s._2 prev_ptr;
  exists_intro (fun v ->
    (prev_ptr + 1) <> 0 /\ s._2 (prev_ptr + 1) == Full v /\ s._1 "ptr" == v /\
    eval_expr (override s._1 "ptr" (Loc prev_ptr), s._2, Ok) (Plus (Var "ptr") (Const 1)) == prev_ptr + 1 /\
    post_len start_ptr k (override s._1 "ptr" (Loc prev_ptr), s._2, Ok)) (Loc curr_ptr);
  exists_intro (fun l -> exists (v : value).
    l <> 0 /\ s._2 l == Full v /\ s._1 "ptr" == v /\
    eval_expr (override s._1 "ptr" (Loc prev_ptr), s._2, Ok) (Plus (Var "ptr") (Const 1)) == l /\
    post_len start_ptr k (override s._1 "ptr" (Loc prev_ptr), s._2, Ok)) (prev_ptr + 1);
  exists_intro (fun x_old -> exists (l : loc) (v : value).
    l <> 0 /\ s._2 l == Full v /\ s._1 "ptr" == v /\
    eval_expr (override s._1 "ptr" x_old, s._2, Ok) (Plus (Var "ptr") (Const 1)) == l /\
    post_len start_ptr k (override s._1 "ptr" x_old, s._2, Ok)) (Loc prev_ptr)

// Demostraciones
let proof_init (start_ptr : loc)
  : isl_triple (is_ok (pre_init start_ptr)) init_vars (kleene_pre (variant start_ptr)) =
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
  let p_assume_raw = ISL_Assume #(variant start_ptr k) (enot (Eq (Var "ptr") (Const 0))) in
  let p_assume = 
    ISL_Consequence (variant start_ptr k) (mid_assume start_ptr k) p_assume_raw () ()
  in

  let p_v_raw =
    framed_load (mid_assume start_ptr k) "v" (Var "ptr") #()
      #(forall_intro (fun st -> forall_intro (fun hp -> forall_intro (fun m ->
        forall_intro (fun g -> forall_intro
          (move_requires (lemma_mid_assume_ghost start_ptr k st hp m g)))))))
  in
  let pf_load = forall_intro (move_requires (lemma_prove_load_v start_ptr k)) in
  let p_v =
    ISL_Consequence (mid_assume start_ptr k) (post_load_v start_ptr k) p_v_raw () pf_load
  in

  let p_sum_raw = ISL_Assign #(post_load_v start_ptr k) "sum" (Plus (Var "sum") (Var "v")) in
  let pf_sum = forall_intro (move_requires (lemma_prove_sum_step start_ptr k)) in
  let p_sum = ISL_Consequence (post_load_v start_ptr k) (post_sum start_ptr k) p_sum_raw () pf_sum in

  let p_len_raw = ISL_Assign #(post_sum start_ptr k) "len" (Plus (Var "len") (Const 1)) in
  let pf_len = forall_intro (move_requires (lemma_prove_len_step start_ptr k)) in
  let p_len = ISL_Consequence (post_sum start_ptr k) (post_len start_ptr k) p_len_raw () pf_len in

  let p_ptr_raw = framed_load (post_len start_ptr k) "ptr" (Plus (Var "ptr") (Const 1)) #() #() in
  let pf_ptr = forall_intro (move_requires (lemma_prove_load_ptr start_ptr k)) in
  let p_ptr = ISL_Consequence (post_len start_ptr k) (variant start_ptr (k + 1)) p_ptr_raw () pf_ptr in
  
  let p_seq1 = ISL_Seq p_len p_ptr in
  let p_tail1 = ISL_Consequence (post_sum start_ptr k) (variant start_ptr (k + 1)) p_seq1 () () in
  let p_seq2 = ISL_Seq p_sum p_tail1 in
  let p_tail2 = ISL_Consequence (post_load_v start_ptr k) (variant start_ptr (k + 1)) p_seq2 () () in
  let p_seq3 = ISL_Seq p_v p_tail2 in
  let p_tail3 = ISL_Consequence (mid_assume start_ptr k) (variant start_ptr (k + 1)) p_seq3 () () in

  let p_raw = ISL_Seq p_assume p_tail3 in
  ISL_Consequence (variant start_ptr k) (variant start_ptr (k + 1)) p_raw () ()

let lemma_kleene (start_ptr : loc)
  : isl_triple (kleene_pre (variant start_ptr)) (Kleene loop_body) (kleene_post (variant start_ptr)) =
  ISL_KleeneVariant (proof_loop_step start_ptr)

let proof_assert (start_ptr : loc)
  : isl_triple (is_ok (pre_assert start_ptr))
    (Seq (Assume (Eq (Var "ptr") (Const 0))) assert_stmt)
    (post_error start_ptr) =
  let p_exit_raw = ISL_Assume #(pre_assert start_ptr) (Eq (Var "ptr") (Const 0)) in
  let p_exit = ISL_Consequence (pre_assert start_ptr) (pre_error start_ptr) p_exit_raw () () in

  let p_cond_err_raw = ISL_Assume #(pre_error start_ptr) (Eq (Var "sum") (Var "len")) in
  let p_cond_err = ISL_Consequence (pre_error start_ptr) (pre_error start_ptr) p_cond_err_raw () () in

  let p_err_raw = ISL_Error #(pre_error start_ptr) in
  let p_branch_err_raw = ISL_Seq p_cond_err p_err_raw in
  let p_branch_err = ISL_Consequence (pre_error start_ptr) (post_error start_ptr) p_branch_err_raw () () in
  
  let p_raw = ISL_Seq p_exit (ISL_ChoiceL p_branch_err) in
  ISL_Consequence (pre_assert start_ptr) (post_error start_ptr) p_raw () ()

let proof_prog_list_sum_len (start_ptr : loc)
  : isl_triple (is_ok (pre_init start_ptr)) prog_list_sum_len (post_error start_ptr) =
  let p_assert = ISL_Consequence (kleene_post (variant start_ptr)) (post_error start_ptr) (proof_assert start_ptr) () () in
  let p_kleene_assert_raw = ISL_Seq (lemma_kleene start_ptr) p_assert in
  let p_kleene_assert = ISL_Consequence (kleene_pre (variant start_ptr)) (post_error start_ptr) p_kleene_assert_raw () () in
  
  let p_raw = ISL_Seq (proof_init start_ptr) p_kleene_assert in
  ISL_Consequence (pre_init start_ptr) (post_error start_ptr) p_raw () ()

#pop-options
