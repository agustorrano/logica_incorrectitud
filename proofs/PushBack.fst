module PushBack

open IncSepLogic
open FStar.Classical
open FStar.FunctionalExtensionality

// Programa y precondicion
let push_back (ptr : var) : stmt =
  Choice
    ((Load "y" (Var ptr)) `Seq`
    ((Free (Var "y")) `Seq`
    ((Alloc "y") `Seq`
    (Store (Var ptr) (Var "y")))))
    Skip

let client (ptr : var) : stmt =
  (Load "x" (Var ptr)) `Seq`
  ((push_back ptr) `Seq` (Store (Var "x") (Const 88)))

let pre_client (ptr : var) (s : state) : prop =
  exists (l_v : loc) (l_a : loc) (val_a : value).
    s._1 ptr == Loc l_v /\
    (points_to l_v (Loc l_a) ** points_to l_a val_a) s

// Parametros logicos de la prueba
noeq type ctx = {
  ptr   : p : var { p <> "x" /\ p <> "y" };
  l_v   : l : loc { l <> 0 }; // estructura
  l_a   : l : loc { l <> 0 /\ l <> l_v }; // celda antigua
  l_b   : l : loc { l <> 0 /\ l <> l_v /\ l <> l_a }; // celda nueva
  val_a : value;
  val_b : value;
}

let post_err (ptr : var) (l_v l_a l_b : loc) (val_b : value) : cond =
  fun s -> s._3 == Er /\
    s._1 ptr == Loc l_v /\ s._1 "x" == Loc l_a /\ s._1 "y" == Loc l_b /\
    (points_to_empty l_a **
      (points_to l_v (Loc l_b) ** points_to l_b val_b)) s

// Descripcion concreta del heap: solo l_v, l_a, l_b pueden ser conocidas
let heap3 (c : ctx) (c1 c2 c3 : cell) : heap =
  on loc (fun l ->
    if l = c.l_v then c1 else if l = c.l_a then c2
    else if l = c.l_b then c3 else Unknown)

let cells (c : ctx) (c1 c2 c3 : cell) : cond =
  fun s -> forall l. s._2 l == heap3 c c1 c2 c3 l

// Aserciones intermedias (heap completo)
let pre_fixed (c : ctx) : cond = fun s ->
  s._1 c.ptr == Loc c.l_v /\
  cells c (Full (Loc c.l_a)) (Full c.val_a) Unknown s

let post_load_x (c : ctx) : cond = fun s ->
  is_ok (pre_fixed c) s /\ s._1 "x" == Loc c.l_a

let post_load_y (c : ctx) : cond = fun s ->
  post_load_x c s /\ s._1 "y" == Loc c.l_a

let post_free_y (c : ctx) : cond = fun s ->
  s._3 == Ok /\ s._1 c.ptr == Loc c.l_v /\
  s._1 "x" == Loc c.l_a /\ s._1 "y" == Loc c.l_a /\
  cells c (Full (Loc c.l_a)) Empty Unknown s

let post_alloc_y (c : ctx) : cond = fun s ->
  s._3 == Ok /\ s._1 c.ptr == Loc c.l_v /\
  s._1 "x" == Loc c.l_a /\ s._1 "y" == Loc c.l_b /\
  cells c (Full (Loc c.l_a)) Empty (Full c.val_b) s

let final_resources (c : ctx) : cond = fun s ->
  s._1 c.ptr == Loc c.l_v /\ s._1 "x" == Loc c.l_a /\ s._1 "y" == Loc c.l_b /\
  cells c (Full (Loc c.l_b)) Empty (Full c.val_b) s

let post_store_v (c : ctx) : cond = is_ok (final_resources c)

let error_fixed (c : ctx) : cond =
  fun s -> s._3 == Er /\ final_resources c s

// Aserciones locales (solo la celda que toca cada comando)
let read_cell (c : ctx) (target : var) : cond = fun s ->
  s._3 == Ok /\ s._1 c.ptr == Loc c.l_v /\ s._1 target == Loc c.l_a /\
  points_to c.l_v (Loc c.l_a) s

let free_pre (c : ctx) : cond = fun s ->
  s._3 == Ok /\ s._1 "y" == Loc c.l_a /\ points_to c.l_a c.val_a s

let free_post (c : ctx) : cond = fun s ->
  s._1 "y" == Loc c.l_a /\ points_to_empty c.l_a s

let alloc_pre (c : ctx) : cond = fun s ->
  s._3 == Ok /\ s._1 "y" == Loc c.l_a /\ emp s

let alloc_post (c : ctx) : cond = fun s ->
  s._1 "y" == Loc c.l_b /\ points_to c.l_b c.val_b s

let store_pre (c : ctx) : cond = fun s ->
  s._3 == Ok /\ s._1 c.ptr == Loc c.l_v /\ s._1 "y" == Loc c.l_b /\
  points_to c.l_v (Loc c.l_a) s

let store_post (c : ctx) : cond = fun s ->
  s._1 c.ptr == Loc c.l_v /\ s._1 "y" == Loc c.l_b /\
  points_to c.l_v (Loc c.l_b) s

let err_pre (c : ctx) : cond = fun s ->
  s._1 "x" == Loc c.l_a /\ points_to_empty c.l_a s

let err_post (c : ctx) : cond = fun s -> s._3 == Er /\ err_pre c s

// Marcos: no dependen del modo ni de las variables que modifica el paso
let frame_load_x (c : ctx) : cond = cells c Unknown (Full c.val_a) Unknown

let frame_load_y (c : ctx) : cond = fun s ->
  s._1 "x" == Loc c.l_a /\ frame_load_x c s

let frame_free (c : ctx) : cond = fun s ->
  s._1 c.ptr == Loc c.l_v /\ s._1 "x" == Loc c.l_a /\
  cells c (Full (Loc c.l_a)) Unknown Unknown s

let frame_alloc (c : ctx) : cond = fun s ->
  s._1 c.ptr == Loc c.l_v /\ s._1 "x" == Loc c.l_a /\
  cells c (Full (Loc c.l_a)) Empty Unknown s

let frame_store (c : ctx) : cond = fun s ->
  s._1 "x" == Loc c.l_a /\ cells c Unknown Empty (Full c.val_b) s

let frame_error (c : ctx) : cond = fun s ->
  s._1 c.ptr == Loc c.l_v /\ s._1 "y" == Loc c.l_b /\
  cells c (Full (Loc c.l_b)) Unknown (Full c.val_b) s

// Lemas "hacia atras": las posts locales implican las de los axiomas
let lemma_read_back (c : ctx) (target : var { target <> c.ptr }) (s : state)
  : Lemma (requires is_ok (read_cell c target) s)
          (ensures is_ok (fun t -> exists l w old.
            eval_expr (override t._1 target old, t._2, Ok) (Var c.ptr) == l /\
            points_to l w t /\ t._1 target == w /\
            read_cell c target (override t._1 target old, t._2, Ok)) s) =
  state_equiv_eq (override s._1 target (Loc c.l_a), s._2, Ok) s;
  exists_intro (fun old ->
    eval_expr (override s._1 target old, s._2, Ok) (Var c.ptr) == c.l_v /\
    points_to c.l_v (Loc c.l_a) s /\ s._1 target == Loc c.l_a /\
    read_cell c target (override s._1 target old, s._2, Ok)) (Loc c.l_a);
  exists_intro (fun w -> exists old.
    eval_expr (override s._1 target old, s._2, Ok) (Var c.ptr) == c.l_v /\
    points_to c.l_v w s /\ s._1 target == w /\
    read_cell c target (override s._1 target old, s._2, Ok)) (Loc c.l_a);
  exists_intro (fun l -> exists w old.
    eval_expr (override s._1 target old, s._2, Ok) (Var c.ptr) == l /\
    points_to l w s /\ s._1 target == w /\
    read_cell c target (override s._1 target old, s._2, Ok)) c.l_v

let lemma_free_back (c : ctx) (s : state)
  : Lemma (requires is_ok (free_post c) s)
          (ensures is_ok (fun t -> exists w.
            points_to_empty (eval_expr t (Var "y")) t /\
            free_pre c (t._1, override t._2 (eval_expr t (Var "y")) (Full w), Ok)) s) =
  exists_intro (fun w -> points_to_empty (eval_expr s (Var "y")) s /\
    free_pre c (s._1, override s._2 (eval_expr s (Var "y")) (Full w), Ok)) c.val_a

let lemma_alloc_back (c : ctx) (s : state)
  : Lemma (requires is_ok (alloc_post c) s)
          (ensures is_ok (fun t -> exists l w.
            t._1 "y" == Loc l /\ l <> 0 /\ points_to l w t /\
            (exists old. alloc_pre c (override t._1 "y" old, override t._2 l Unknown, Ok))) s) =
  exists_intro (fun old ->
    alloc_pre c (override s._1 "y" old, override s._2 c.l_b Unknown, Ok)) (Loc c.l_a);
  exists_intro (fun w -> s._1 "y" == Loc c.l_b /\ c.l_b <> 0 /\ points_to c.l_b w s /\
    (exists old. alloc_pre c (override s._1 "y" old, override s._2 c.l_b Unknown, Ok))) c.val_b;
  exists_intro (fun l -> exists w. s._1 "y" == Loc l /\ l <> 0 /\ points_to l w s /\
    (exists old. alloc_pre c (override s._1 "y" old, override s._2 l Unknown, Ok))) c.l_b

let lemma_store_back (c : ctx) (s : state)
  : Lemma (requires is_ok (store_post c) s)
          (ensures is_ok (fun t ->
            points_to (eval_expr t (Var c.ptr)) (eval_value t (Var "y")) t /\
            (exists old. store_pre c (t._1, override t._2 (eval_expr t (Var c.ptr)) (Full old), Ok))) s) =
  exists_intro (fun old -> store_pre c
    (s._1, override s._2 (eval_expr s (Var c.ptr)) (Full old), Ok)) (Loc c.l_a)

let initial_implies (c : ctx) (s : state)
  : Lemma (requires pre_fixed c s) (ensures pre_client c.ptr s) =
  introduce_frame (points_to c.l_v (Loc c.l_a)) (points_to c.l_a c.val_a) s
    (singleton_full_heap c.l_v (Loc c.l_a)) (singleton_full_heap c.l_a c.val_a);
  exists_intro (fun v -> s._1 c.ptr == Loc c.l_v /\
    (points_to c.l_v (Loc c.l_a) ** points_to c.l_a v) s) c.val_a;
  exists_intro (fun a -> exists v. s._1 c.ptr == Loc c.l_v /\
    (points_to c.l_v (Loc a) ** points_to a v) s) c.l_a;
  exists_intro (fun a -> exists b v. s._1 c.ptr == Loc a /\
    (points_to a (Loc b) ** points_to b v) s) c.l_v

// Separaciones del heap completo en footprint ** marco
let split_load_x (c : ctx) (s : state)
  : Lemma (requires post_load_x c s)
          (ensures (is_ok (read_cell c "x") ** frame_load_x c) s) =
  introduce_frame (is_ok (read_cell c "x")) (frame_load_x c) s
    (singleton_full_heap c.l_v (Loc c.l_a))
    (heap3 c Unknown (Full c.val_a) Unknown)

let split_load_y (c : ctx) (s : state)
  : Lemma (requires post_load_y c s)
          (ensures (is_ok (read_cell c "y") ** frame_load_y c) s) =
  introduce_frame (is_ok (read_cell c "y")) (frame_load_y c) s
    (singleton_full_heap c.l_v (Loc c.l_a))
    (heap3 c Unknown (Full c.val_a) Unknown)

let split_free (c : ctx) (s : state)
  : Lemma (requires post_free_y c s)
          (ensures (is_ok (free_post c) ** frame_free c) s) =
  introduce_frame (is_ok (free_post c)) (frame_free c) s
    (singleton_empty_heap c.l_a)
    (heap3 c (Full (Loc c.l_a)) Unknown Unknown)

let split_alloc (c : ctx) (s : state)
  : Lemma (requires post_alloc_y c s)
          (ensures (is_ok (alloc_post c) ** frame_alloc c) s) =
  introduce_frame (is_ok (alloc_post c)) (frame_alloc c) s
    (singleton_full_heap c.l_b c.val_b)
    (heap3 c (Full (Loc c.l_a)) Empty Unknown)

let split_store (c : ctx) (s : state)
  : Lemma (requires post_store_v c s)
          (ensures (is_ok (store_post c) ** frame_store c) s) =
  introduce_frame (is_ok (store_post c)) (frame_store c) s
    (singleton_full_heap c.l_v (Loc c.l_b))
    (heap3 c Unknown Empty (Full c.val_b))

let split_error (c : ctx) (s : state)
  : Lemma (requires error_fixed c s)
          (ensures (err_post c ** frame_error c) s) =
  introduce_frame (err_post c) (frame_error c) s
    (singleton_empty_heap c.l_a)
    (heap3 c (Full (Loc c.l_b)) Unknown (Full c.val_b))

// Un paso por funcion
let step_load_x (c : ctx)
  : isl_triple (is_ok (pre_fixed c)) (Load "x" (Var c.ptr)) (post_load_x c) =
  let local = ISL_Consequence (read_cell c "x") (is_ok (read_cell c "x"))
    (ISL_Load #(read_cell c "x") "x" (Var c.ptr)) ()
    (forall_intro (move_requires (lemma_read_back c "x"))) in
  ISL_Consequence (pre_fixed c) (post_load_x c)
    (ISL_Frame (frame_load_x c) local ()) ()
    (forall_intro (move_requires (split_load_x c)))

let step_load_y (c : ctx)
  : isl_triple (is_ok (post_load_x c)) (Load "y" (Var c.ptr)) (post_load_y c) =
  let local = ISL_Consequence (read_cell c "y") (is_ok (read_cell c "y"))
    (ISL_Load #(read_cell c "y") "y" (Var c.ptr)) ()
    (forall_intro (move_requires (lemma_read_back c "y"))) in
  ISL_Consequence (post_load_x c) (post_load_y c)
    (ISL_Frame (frame_load_y c) local ()) ()
    (forall_intro (move_requires (split_load_y c)))

let step_free (c : ctx)
  : isl_triple (is_ok (post_load_y c)) (Free (Var "y")) (post_free_y c) =
  let local = ISL_Consequence (free_pre c) (is_ok (free_post c))
    (ISL_Free #(free_pre c) (Var "y")) ()
    (forall_intro (move_requires (lemma_free_back c))) in
  ISL_Consequence (post_load_y c) (post_free_y c)
    (ISL_Frame (frame_free c) local ()) ()
    (forall_intro (move_requires (split_free c)))

let step_alloc (c : ctx)
  : isl_triple (is_ok (post_free_y c)) (Alloc "y") (post_alloc_y c) =
  let local = ISL_Consequence (alloc_pre c) (is_ok (alloc_post c))
    (ISL_Alloc1 #(alloc_pre c) "y") ()
    (forall_intro (move_requires (lemma_alloc_back c))) in
  ISL_Consequence (post_free_y c) (post_alloc_y c)
    (ISL_Frame (frame_alloc c) local ()) ()
    (forall_intro (move_requires (split_alloc c)))

let step_store (c : ctx)
  : isl_triple (is_ok (post_alloc_y c)) (Store (Var c.ptr) (Var "y")) (post_store_v c) =
  let local = ISL_Consequence (store_pre c) (is_ok (store_post c))
    (ISL_Store #(store_pre c) (Var c.ptr) (Var "y")) ()
    (forall_intro (move_requires (lemma_store_back c))) in
  ISL_Consequence (post_alloc_y c) (post_store_v c)
    (ISL_Frame (frame_store c) local ()) ()
    (forall_intro (move_requires (split_store c)))

let step_error (c : ctx)
  : isl_triple (is_ok (post_store_v c)) (Store (Var "x") (Const 88)) (error_fixed c) =
  let local = ISL_Consequence (is_ok (err_pre c)) (err_post c)
    (ISL_StoreEr #(is_ok (err_pre c)) (Var "x") (Const 88)) () () in
  ISL_Consequence (post_store_v c) (error_fixed c)
    (ISL_Frame (frame_error c) local ()) ()
    (forall_intro (move_requires (split_error c)))

// Composicion
let proof_push_back (c : ctx)
  : isl_triple (is_ok (post_load_x c)) (push_back c.ptr) (post_store_v c) =
  let branch = ISL_Seq (step_load_y c) (ISL_Seq (step_free c)
    (ISL_Seq (step_alloc c) (step_store c))) in
  ISL_Consequence (post_load_x c) (post_store_v c) (ISL_ChoiceL branch) () ()

let proof_client_ctx (c : ctx)
  : isl_triple (is_ok (pre_client c.ptr)) (client c.ptr)
    (post_err c.ptr c.l_v c.l_a c.l_b c.val_b) =
  let all = ISL_Seq (step_load_x c) (ISL_Seq (proof_push_back c) (step_error c)) in
  let fixed = ISL_Consequence (pre_fixed c) (error_fixed c) all () () in
  ISL_Consequence (pre_client c.ptr) (post_err c.ptr c.l_v c.l_a c.l_b c.val_b) fixed
    (forall_intro (move_requires (initial_implies c))) ()

let proof_client
  (ptr : var { ptr <> "x" /\ ptr <> "y" })
  (l_v : loc { l_v <> 0 })
  (l_a : loc { l_a <> 0 /\ l_a <> l_v })
  (l_b : loc { l_b <> 0 /\ l_b <> l_v /\ l_b <> l_a })
  (val_a val_b : value)
  : isl_triple (is_ok (pre_client ptr)) (client ptr)
    (post_err ptr l_v l_a l_b val_b) =
  proof_client_ctx { ptr; l_v; l_a; l_b; val_a; val_b }
