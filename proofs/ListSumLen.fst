module ListSumLen

open IncSepLogic
open FStar.Classical
open FStar.FunctionalExtensionality
open FStar.IndefiniteDescription

let ( ||| ) = Choice
let enot (e : expr) : expr = Minus (Const 1) e

// Programa
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

// Listas enlazadas
let rec list_seg (i j : loc) (xs : list value) : Tot cond (decreases xs) =
  match xs with
  | [] -> fun s -> emp s /\ i == j
  | x :: xss -> fun s -> 
    exists (next : loc).
      (points_to i x ** points_to (i + 1) (Loc next) ** list_seg next j xss) s

let rec ones (n : nat) : list value =
  if n = 0 then [] else Nat 1 :: ones (n - 1)

let heap_only (hp : heap) : state = on var (fun _ -> Nat 0), hp, Ok

// Load con marco (framed_load): las tres partes, en forma generica
let g_old = "list_old" // valor viejo
let g_addr = "list_addr" // dirección leída
let g_value = "list_value" // valor leído

let ghost_free (pre : cond) : prop =
  forall (st : store) (hp : heap) (m : term_mode) (g : var) (v : value).
    (g == g_old \/ g == g_addr \/ g == g_value) ==>
    (pre (override st g v, hp, m) <==> pre (st, hp, m))
 
let ghost_free_intro (pre : cond)
  (f : (st : store) -> (hp : heap) -> (m : term_mode) -> (g : var) -> (v : value) ->
    Lemma (requires g == g_old \/ g == g_addr \/ g == g_value)
          (ensures pre (override st g v, hp, m) <==> pre (st, hp, m)))
  : Lemma (ghost_free pre) =
  forall_intro (fun st -> forall_intro (fun hp ->
    forall_intro (fun m -> forall_intro (fun g ->
      forall_intro (move_requires (f st hp m g))))))

let ghost_updates (pre : cond) (st : store) (hp : heap) (m : term_mode)
  (wv wa wo : value) (#free : squash (ghost_free pre))
  : Lemma (ensures (pre (override (override (override st g_value wv) g_addr wa) g_old wo, hp, m)
            <==> pre (st, hp, m))) =
  let st1 = override st g_value wv in
  let st2 = override st1 g_addr wa in
  ()

let load_fresh (x : var) (e : expr) : prop =
  x <> g_old /\ x <> g_addr /\ x <> g_value /\
  ~(fv_expr e g_old) /\ ~(fv_expr e g_addr) /\ ~(fv_expr e g_value)

let load_addr (st : store) = eval_expr' st (Var g_addr)

// Postcondicion que da framed_load (la forma "global" del load)
let load_post (pre : cond) (x : var) (e : expr) : cond =
  fun s -> s._3 == Ok /\
    exists (x_old : value) (l : loc) (v : value).
      points_to_flex l v s /\ s._1 x == v /\
      eval_expr (override s._1 x x_old, s._2, Ok) e == l /\
      pre (override s._1 x x_old, s._2, Ok)

let load_post_intro (pre : cond) (x : var) (e : expr) (s : state)
  (x_old : value) (l : loc) (v : value)
  : Lemma (requires points_to_flex l v s /\ s._1 x == v /\
                    eval_expr (override s._1 x x_old, s._2, Ok) e == l /\
                    pre (override s._1 x x_old, s._2, Ok) /\ s._3 == Ok)
          (ensures load_post pre x e s) = ()

// ---------- 1. Parte local: solo la celda leida ----------
let read_cell (x : var) (e : expr) : cond =
  fun s -> s._3 == Ok /\ s._1 x == s._1 g_old /\
    eval_expr s e == load_addr s._1 /\
    points_to (load_addr s._1) (s._1 g_value) s

let read_cell_post (x : var) (e : expr) : cond =
  fun s -> s._3 == Ok /\ s._1 x == s._1 g_value /\
    eval_expr (override s._1 x (s._1 g_old), s._2, Ok) e == load_addr s._1 /\
    points_to (load_addr s._1) (s._1 g_value) s

let lemma_read_back (x : var) (e : expr)
  (#fresh : squash (load_fresh x e)) (s : state)
  : Lemma (requires read_cell_post x e s)
          (ensures exists (l : loc) (v old : value).
            eval_expr (override s._1 x old, s._2, Ok) e == l /\
            points_to l v s /\ s._1 x == v /\
            read_cell x e (override s._1 x old, s._2, Ok)) =
  eval_expr_fresh s (Var g_addr) x (s._1 g_old);
  exists_intro (fun old ->
    eval_expr (override s._1 x old, s._2, Ok) e == load_addr s._1 /\
    points_to (load_addr s._1) (s._1 g_value) s /\ s._1 x == s._1 g_value /\
    read_cell x e (override s._1 x old, s._2, Ok)) (s._1 g_old);
  exists_intro (fun v -> exists (old : value).
    eval_expr (override s._1 x old, s._2, Ok) e == load_addr s._1 /\
    points_to (load_addr s._1) v s /\ s._1 x == v /\
    read_cell x e (override s._1 x old, s._2, Ok)) (s._1 g_value);
  exists_intro (fun l -> exists (v old : value).
    eval_expr (override s._1 x old, s._2, Ok) e == l /\
    points_to l v s /\ s._1 x == v /\
    read_cell x e (override s._1 x old, s._2, Ok)) (load_addr s._1)

// ---------- 2. Marco: pre vale sobre el heap completo ----------
let frame_load (pre : cond) (x : var) : cond =
  fun s -> s._2 (load_addr s._1) == Unknown /\
    pre (override s._1 x (s._1 g_old), override s._2 (load_addr s._1) (Full (s._1 g_value)), Ok)

let frame_load_indep_aux (pre : cond) (x : var) (e : expr)
  (#fresh : squash (load_fresh x e))
  (st1 st2 : store) (hp : heap) (m1 m2 : term_mode)
  : Lemma (requires match_except_vars (modifies (Load x e)) st1 st2)
          (ensures (frame_load pre x (st1, hp, m1) <==>
            frame_load pre x (st2, hp, m2))) =
  state_equiv_eq (override st1 x (st1 g_old), hp, Ok) (override st2 x (st2 g_old), hp, Ok)

let frame_load_indep (pre : cond) (x : var) (e : expr) (#fresh : squash (load_fresh x e))
  : Lemma (independent_on_vars (modifies (Load x e)) (frame_load pre x)) =
  forall_intro (fun st1 -> forall_intro (fun st2 -> forall_intro (fun hp ->
    forall_intro (fun m1 -> forall_intro (move_requires (frame_load_indep_aux pre x e #() st1 st2 hp m1))))))

// ---------- 3. Consequence: local ** marco <-> aserciones ----------
let split_cell (hp : heap) (l : loc) (v : value)
  : Lemma (requires hp l == Full v)
          (ensures heaps_disjoint (singleton_full_heap l v) (heap_without hp l) /\
            hp == heap_union (singleton_full_heap l v) (heap_without hp l)) =
  extensionality loc (fun _ -> cell) hp ((singleton_full_heap l v) <+> (heap_without hp l))

#push-options "--fuel 3 --ifuel 1 --z3rlimit 100"

let join_load (pre : cond) (x : var) (e : expr)
  (#free : squash (ghost_free pre)) (s : state)
  : Lemma (requires exists_var g_value
            (exists_var g_addr (exists_var g_old (read_cell x e ** frame_load pre x))) s)
          (ensures pre s) =
  let wv = indefinite_description_ghost value (fun wv ->
    exists_var g_addr (exists_var g_old (read_cell x e ** frame_load pre x)) (override s._1 g_value wv, s._2, s._3))
  in
  let wa = indefinite_description_ghost value (fun wa ->
    exists_var g_old (read_cell x e ** frame_load pre x) (override (override s._1 g_value wv) g_addr wa, s._2, s._3))
  in
  let wo = indefinite_description_ghost value (fun wo ->
    (read_cell x e ** frame_load pre x) (override (override (override s._1 g_value wv) g_addr wa) g_old wo, s._2, s._3))
  in
  let st = override (override (override s._1 g_value wv) g_addr wa) g_old wo in
  let h1 = indefinite_description_ghost heap (fun h1 -> exists h2.
    heaps_disjoint h1 h2 /\ s._2 == heap_union h1 h2 /\
    read_cell x e (st, h1, s._3) /\ frame_load pre x (st, h2, s._3))
  in
  let h2 = indefinite_description_ghost heap (fun h2 ->
    heaps_disjoint h1 h2 /\ s._2 == heap_union h1 h2 /\
    read_cell x e (st, h1, s._3) /\ frame_load pre x (st, h2, s._3))
  in
  state_equiv_eq (override st x (st g_old), override h2 (load_addr st) (Full (st g_value)), Ok) (st, s._2, Ok);
  ghost_updates pre s._1 s._2 Ok wv wa wo #()

let split_load (pre : cond) (x : var) (e : expr)
  (#fresh : squash (load_fresh x e)) (#free : squash (ghost_free pre))
  (s : state)
  : Lemma (requires load_post pre x e s)
          (ensures exists_var g_value
            (exists_var g_addr (exists_var g_old
              (read_cell_post x e ** frame_load pre x))) s) =
  let old = indefinite_description_ghost value (fun old ->
    exists (l : loc) (v : value). points_to_flex l v s /\
      s._1 x == v /\ eval_expr (override s._1 x old, s._2, Ok) e == l /\
      pre (override s._1 x old, s._2, Ok))
  in
  let l = eval_expr (override s._1 x old, s._2, Ok) e in
  let v = s._1 x in
  let st = override (override (override s._1 g_value v) g_addr (Loc l)) g_old old in
  let h1 = singleton_full_heap l v in
  let h2 = heap_without s._2 l in
  split_cell s._2 l v;
  state_equiv_eq (override s._1 x old, s._2, Ok) (override s._1 x old, override h2 l (Full v), Ok);
  eval_expr_fresh (override s._1 x old, s._2, Ok) e g_value v;
  eval_expr_fresh (override (override s._1 x old) g_value v, s._2, Ok) e g_addr (Loc l);
  eval_expr_fresh (override (override (override s._1 x old) g_value v) g_addr (Loc l), s._2, Ok) e g_old old;
  state_equiv_eq (override st x (st g_old), s._2, Ok)
    (override (override (override (override s._1 x old) g_value v) g_addr (Loc l)) g_old old, s._2, Ok);
  ghost_updates pre (override s._1 x old) s._2 Ok v (Loc l) old #();
  introduce_frame (read_cell_post x e) (frame_load pre x) (st, s._2, Ok) h1 h2;
  exists_intro (fun w -> (read_cell_post x e ** frame_load pre x)
    (override (override (override s._1 g_value v) g_addr (Loc l)) g_old w, s._2, s._3)) old;
  exists_intro (fun w -> exists_var g_old (read_cell_post x e ** frame_load pre x)
    (override (override s._1 g_value v) g_addr w, s._2, s._3)) (Loc l);
  exists_intro (fun w -> exists_var g_addr
    (exists_var g_old (read_cell_post x e ** frame_load pre x))
    (override s._1 g_value w, s._2, s._3)) v

// ---------- Las tres partes juntas ----------
let framed_load (pre : cond) (x : var) (e : expr)
  (#fresh : squash (load_fresh x e)) (#free : squash (ghost_free pre))
  : isl_triple (is_ok pre) (Load x e) (load_post pre x e) =
  let local_pf = ISL_Consequence (read_cell x e) (read_cell_post x e)
    (ISL_Load #(read_cell x e) x e) ()
    (forall_intro (move_requires (lemma_read_back x e #()))) in
  let framed = ISL_Frame (frame_load pre x) local_pf (frame_load_indep pre x e #()) in
  let hidden = ISL_Exists g_value
    (ISL_Exists g_addr (ISL_Exists g_old framed ()) ()) () in
  ISL_Consequence pre (load_post pre x e) hidden
    (forall_intro (move_requires (join_load pre x e #())))
    (forall_intro (move_requires (split_load pre x e #() #())))

// Aserciones
let rec history (start_ptr curr_ptr : loc) (n : nat) (k : nat) (hp : heap)
  : GTot prop (decreases k) =
  let s = heap_only hp in
  if k = 0 then
    curr_ptr == start_ptr /\
    list_seg start_ptr 0 (ones n) s
  else exists (prev_ptr : loc).
    points_to_flex prev_ptr (Nat 1) s /\
    points_to_flex (prev_ptr + 1) (Loc curr_ptr) s /\
    history start_ptr prev_ptr n (k - 1) hp

let pre_init (start_ptr : loc) (n : nat) : cond =
  fun s -> s._3 == Ok /\
    s._1 "ptr" == Loc start_ptr /\
    history start_ptr start_ptr n 0 s._2

let post_init_sum (start_ptr : loc) (n : nat) : cond =
  fun s -> pre_init start_ptr n s /\ s._1 "sum" == Nat 0

let variant (start_ptr : loc) (n : nat) (k : nat) : cond =
  fun s ->
    k <= n /\ s._3 == Ok /\
    s._1 "sum" == Nat k /\ s._1 "len" == Nat k /\
    (k > 0 ==> s._1 "v" == Nat 1) /\
    exists (curr_ptr : loc).
      s._1 "ptr" == Loc curr_ptr /\
      history start_ptr curr_ptr n k s._2

let post_assume (start_ptr : loc) (n : nat) (k : nat) : cond =
  fun s -> variant start_ptr n k s /\ eval_expr s (enot (Eq (Var "ptr") (Const 0))) <> 0

let step_state (start_ptr : loc) (n : nat) (k : nat) (sum len : nat) : cond =
  fun s ->
    k < n /\ s._3 == Ok /\
    s._1 "sum" == Nat sum /\ s._1 "len" == Nat len /\
    s._1 "v" == Nat 1 /\
    exists (curr_ptr : loc).
      s._1 "ptr" == Loc curr_ptr /\
      history start_ptr curr_ptr n k s._2 /\
      points_to_flex curr_ptr (Nat 1) s

let post_load_v (start_ptr : loc) (n : nat) (k : nat) : cond =
  fun s -> post_assume start_ptr n k s /\ step_state start_ptr n k k k s

let post_sum (start_ptr : loc) (n : nat) (k : nat) : cond =
  step_state start_ptr n k (k + 1) k

let post_len (start_ptr : loc) (n : nat) (k : nat) : cond =
  step_state start_ptr n k (k + 1) (k + 1)

let post_loop (start_ptr : loc) (n : nat) : cond =
  fun s -> exists (k : nat). variant start_ptr n k s

let post_exit (start_ptr : loc) (n : nat) : cond =
  fun s ->
    variant start_ptr n n s /\ s._1 "ptr" == Loc 0 /\
    eval_expr s (Eq (Var "sum") (Var "len")) <> 0

let post_err (start_ptr : loc) (n : nat) : cond =
  fun s -> s._3 == Er /\ post_exit start_ptr n (s._1, s._2, Ok)

// Lemas
let ghost_free_post_assume (start_ptr : loc) (n : nat) (k : nat)
  (st : store) (hp : heap) (m : term_mode) (g : var) (v : value)
  : Lemma (requires (g == g_old \/ g == g_addr \/ g == g_value))
          (ensures (post_assume start_ptr n k (override st g v, hp, m) <==>
            post_assume start_ptr n k (st, hp, m))) =
  eval_expr_fresh (st, hp, m) (enot (Eq (Var "ptr") (Const 0))) g v

let ghost_free_post_len (start_ptr : loc) (n : nat) (k : nat)
  (st : store) (hp : heap) (m : term_mode) (g : var) (v : value)
  : Lemma (requires (g == g_old \/ g == g_addr \/ g == g_value))
          (ensures (post_len start_ptr n k (override st g v, hp, m) <==>
            post_len start_ptr n k (st, hp, m))) =
  ()

let lemma_load_v (start_ptr : loc) (n : nat) (k : nat) (s : state)
  : Lemma (requires post_load_v start_ptr n k s)
          (ensures load_post (post_assume start_ptr n k) "v" (Var "ptr") s) =
  let curr_ptr = indefinite_description_ghost
    loc (fun curr_ptr -> s._1 "ptr" == Loc curr_ptr /\ points_to_flex curr_ptr (Nat 1) s)
  in
  state_equiv_eq (override s._1 "v" (s._1 "v"), s._2, Ok) s;
  load_post_intro (post_assume start_ptr n k) "v" (Var "ptr") s (s._1 "v") curr_ptr (Nat 1)

let lemma_sum (start_ptr : loc) (n : nat) (k : nat) (s : state)
  : Lemma (requires (post_sum start_ptr n k s))
          (ensures (is_ok (fun s0 -> exists (st_init : store).
            post_load_v start_ptr n k (st_init, s0._2, s0._3) /\
            s0._1 "sum" == Nat (eval_expr (st_init, s0._2, s0._3) (Plus (Var "sum") (Var "v"))) /\
            (forall (y : var). y <> "sum" ==> s0._1 y == st_init y)) s)) =
  let st_init = override s._1 "sum" (Nat k) in
  exists_intro (fun (st_init : store) ->
    post_load_v start_ptr n k (st_init, s._2, s._3) /\
    s._1 "sum" == Nat (eval_expr (st_init, s._2, s._3) (Plus (Var "sum") (Var "v"))) /\
    (forall (y : var). y <> "sum" ==> s._1 y == st_init y)) st_init

let lemma_len (start_ptr : loc) (n : nat) (k : nat) (s : state)
  : Lemma (requires (post_len start_ptr n k s))
          (ensures (is_ok (fun s0 -> exists (st_init : store).
            post_sum start_ptr n k (st_init, s0._2, s0._3) /\
            s0._1 "len" == Nat (eval_expr (st_init, s0._2, s0._3) (Plus (Var "len") (Const 1))) /\
            (forall (y : var). y <> "len" ==> s0._1 y == st_init y)) s)) =
  let st_init = override s._1 "len" (Nat k) in
  exists_intro (fun (st_init : store) ->
    post_sum start_ptr n k (st_init, s._2, s._3) /\
    s._1 "len" == Nat (eval_expr (st_init, s._2, s._3) (Plus (Var "len") (Const 1))) /\
    (forall (y : var). y <> "len" ==> s._1 y == st_init y)) st_init

let eval_pointer (st : store) (hp : heap) (p : loc)
  : Lemma (ensures eval_expr (override st "ptr" (Loc p), hp, Ok) (Plus (Var "ptr") (Const 1)) == p + 1) =
  assert_norm (eval_expr (override st "ptr" (Loc p), hp, Ok)
    (Plus (Var "ptr") (Const 1)) == p + 1)

let lemma_load_ptr (start_ptr : loc) (n : nat) (k : nat) (s : state)
  : Lemma (requires variant start_ptr n (k + 1) s)
          (ensures load_post (post_len start_ptr n k) "ptr" (Plus (Var "ptr") (Const 1)) s) =
  let curr_ptr = indefinite_description_ghost
    loc (fun curr_ptr -> s._1 "ptr" == Loc curr_ptr /\ history start_ptr curr_ptr n (k + 1) s._2)
  in
  let hs = heap_only s._2 in
  let prev_ptr = indefinite_description_ghost loc (fun prev_ptr ->
    points_to_flex prev_ptr (Nat 1) hs /\
    points_to_flex (prev_ptr + 1) (Loc curr_ptr) hs /\
    history start_ptr prev_ptr n k s._2)
  in
  exists_intro (fun p ->
    (override s._1 "ptr" (Loc prev_ptr)) "ptr" == Loc p /\
    history start_ptr p n k s._2 /\
    points_to_flex p (Nat 1) (override s._1 "ptr" (Loc prev_ptr), s._2, Ok)) prev_ptr;
  eval_pointer s._1 s._2 prev_ptr;
  load_post_intro (post_len start_ptr n k) "ptr" (Plus (Var "ptr") (Const 1)) s (Loc prev_ptr) (prev_ptr + 1) (Loc curr_ptr)

#pop-options

// Inicializacion
// sum := 0
let step_init_sum (start_ptr : loc) (n : nat)
  : isl_triple (is_ok (pre_init start_ptr n)) (Assign "sum" (Const 0)) (post_init_sum start_ptr n) =
  ISL_Consequence (pre_init start_ptr n) (post_init_sum start_ptr n)
    (ISL_Assign #(pre_init start_ptr n) "sum" (Const 0)) () ()

// len := 0
let step_init_len (start_ptr : loc) (n : nat)
  : isl_triple (is_ok (post_init_sum start_ptr n)) (Assign "len" (Const 0))
      (kleene_pre (variant start_ptr n)) =
  ISL_Consequence (post_init_sum start_ptr n) (kleene_pre (variant start_ptr n))
    (ISL_Assign #(post_init_sum start_ptr n) "len" (Const 0)) () ()

let proof_init (start_ptr : loc) (n : nat)
  : isl_triple (is_ok (pre_init start_ptr n)) init_vars (kleene_pre (variant start_ptr n)) =
  ISL_Consequence (pre_init start_ptr n) (kleene_pre (variant start_ptr n))
    (ISL_Seq (step_init_sum start_ptr n) (step_init_len start_ptr n)) () ()

// Cuerpo del bucle: un paso por funcion (vuelta k -> k + 1)
// 1. assume(ptr <> 0): todavia no se llego al final de la lista.
let step_assume (start_ptr : loc) (n : nat) (k : nat)
  : isl_triple (is_ok (variant start_ptr n k)) (Assume (enot (Eq (Var "ptr") (Const 0))))
      (post_assume start_ptr n k) =
  ISL_Consequence (variant start_ptr n k) (post_assume start_ptr n k)
    (ISL_Assume #(variant start_ptr n k) (enot (Eq (Var "ptr") (Const 0)))) () ()

// 2. v := [ptr]: leer el valor del nodo actual (load con marco).
let step_load_v (start_ptr : loc) (n : nat) (k : nat)
  : isl_triple (is_ok (post_assume start_ptr n k)) (Load "v" (Var "ptr"))
      (post_load_v start_ptr n k) =
  let load = framed_load (post_assume start_ptr n k) "v" (Var "ptr") #()
    #(ghost_free_intro (post_assume start_ptr n k) (ghost_free_post_assume start_ptr n k)) in
  ISL_Consequence (post_assume start_ptr n k) (post_load_v start_ptr n k) load ()
    (forall_intro (move_requires (lemma_load_v start_ptr n k)))

// 3. sum := sum + v
let step_sum (start_ptr : loc) (n : nat) (k : nat)
  : isl_triple (is_ok (post_load_v start_ptr n k)) (Assign "sum" (Plus (Var "sum") (Var "v")))
      (post_sum start_ptr n k) =
  ISL_Consequence (post_load_v start_ptr n k) (post_sum start_ptr n k)
    (ISL_Assign #(post_load_v start_ptr n k) "sum" (Plus (Var "sum") (Var "v"))) ()
    (forall_intro (move_requires (lemma_sum start_ptr n k)))

// 4. len := len + 1
let step_len (start_ptr : loc) (n : nat) (k : nat)
  : isl_triple (is_ok (post_sum start_ptr n k)) (Assign "len" (Plus (Var "len") (Const 1)))
      (post_len start_ptr n k) =
  ISL_Consequence (post_sum start_ptr n k) (post_len start_ptr n k)
    (ISL_Assign #(post_sum start_ptr n k) "len" (Plus (Var "len") (Const 1))) ()
    (forall_intro (move_requires (lemma_len start_ptr n k)))

// 5. ptr := [ptr + 1]: avanzar al siguiente nodo (load con marco).
let step_load_ptr (start_ptr : loc) (n : nat) (k : nat)
  : isl_triple (is_ok (post_len start_ptr n k)) (Load "ptr" (Plus (Var "ptr") (Const 1)))
      (variant start_ptr n (k + 1)) =
  let load = framed_load (post_len start_ptr n k) "ptr" (Plus (Var "ptr") (Const 1)) #()
    #(ghost_free_intro (post_len start_ptr n k) (ghost_free_post_len start_ptr n k)) in
  ISL_Consequence (post_len start_ptr n k) (variant start_ptr n (k + 1)) load ()
    (forall_intro (move_requires (lemma_load_ptr start_ptr n k)))

let proof_loop_step (start_ptr : loc) (n : nat) (k : nat)
  : isl_triple (is_ok (variant start_ptr n k)) loop_body (is_ok (variant start_ptr n (k + 1))) =
  let body = ISL_Seq (step_assume start_ptr n k)
    (ISL_Seq (step_load_v start_ptr n k) (ISL_Seq (step_sum start_ptr n k)
    (ISL_Seq (step_len start_ptr n k) (step_load_ptr start_ptr n k)))) in
  ISL_Consequence (variant start_ptr n k) (is_ok (variant start_ptr n (k + 1))) body () ()

// El bucle: con el variante, n vueltas llevan de variant 0 a variant n.
let proof_loop (start_ptr : loc) (n : nat)
  : isl_triple (kleene_pre (variant start_ptr n)) (Kleene loop_body)
      (kleene_post (variant start_ptr n)) =
  ISL_KleeneVariant (proof_loop_step start_ptr n)

// Salida del bucle y assert
// assume(ptr = 0): se llego al final de la lista, despues de n vueltas.
let step_exit (start_ptr : loc) (n : nat)
  : isl_triple (is_ok (post_loop start_ptr n)) (Assume (Eq (Var "ptr") (Const 0)))
      (post_exit start_ptr n) =
  ISL_Consequence (post_loop start_ptr n) (post_exit start_ptr n)
    (ISL_Assume #(post_loop start_ptr n) (Eq (Var "ptr") (Const 0))) () ()

// assert: se toma la rama de error, porque sum = len.
let step_assert (start_ptr : loc) (n : nat)
  : isl_triple (is_ok (post_exit start_ptr n)) assert_stmt (post_err start_ptr n) =
  let branch_err = ISL_Seq (ISL_Assume #(post_exit start_ptr n) (Eq (Var "sum") (Var "len")))
                           ISL_Error in
  ISL_ChoiceL branch_err

let proof_assert (start_ptr : loc) (n : nat)
  : isl_triple (is_ok (post_loop start_ptr n))
    (Seq (Assume (Eq (Var "ptr") (Const 0))) assert_stmt)
    (post_err start_ptr n) =
  ISL_Consequence (post_loop start_ptr n) (post_err start_ptr n)
    (ISL_Seq (step_exit start_ptr n) (step_assert start_ptr n)) () ()

// Composicion
let proof_list_sum_len (start_ptr : loc) (n : nat)
  : isl_triple (is_ok (pre_init start_ptr n)) prog_list_sum_len (post_err start_ptr n) =
  let p_assert = ISL_Consequence (kleene_post (variant start_ptr n)) (post_err start_ptr n)
    (proof_assert start_ptr n) () () in
  let p_loop = ISL_Consequence (kleene_pre (variant start_ptr n)) (post_err start_ptr n)
    (ISL_Seq (proof_loop start_ptr n) p_assert) () () in
  ISL_Consequence (pre_init start_ptr n) (post_err start_ptr n)
    (ISL_Seq (proof_init start_ptr n) p_loop) () ()
