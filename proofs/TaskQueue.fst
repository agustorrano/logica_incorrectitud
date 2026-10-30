module TaskQueue

open IncSepLogic
open FStar.FunctionalExtensionality

let ( ||| ) = Choice

// Abstraccion del camino defectuoso de taskqueue.c:
//
//   if (q->size == q->capacity) {
//     q->items = realloc(q->items, ...);
//   }
//   lowest->score = avg;
//
// Cuando realloc mueve el arreglo, el puntero lowest queda colgando. En el
// lenguaje de IncSepLogic representamos ese movimiento por la liberacion de la
// celda apuntada por lowest; la escritura posterior modela lowest->score = avg.
let queue_push_realloc_path : stmt =
  Assume (Eq (Var "q_size") (Var "q_capacity")) `Seq`
  Free (Var "lowest")

let apply_catchup_bonus_realloc_path : stmt =
  queue_push_realloc_path `Seq`
  Store (Var "lowest") (Var "avg")

let pre_lowest_in_full_queue (l_low : loc) : cond =
  fun s ->
    s._1 "q_size" == Nat 4 /\
    s._1 "q_capacity" == Nat 4 /\
    s._1 "avg" == Nat 16 /\
    s._1 "lowest" == Loc l_low /\
    points_to l_low (Nat 5) s

let pre_realloc_branch (l_low : loc) : cond =
  fun s ->
    s._3 == Ok /\
    pre_lowest_in_full_queue l_low s /\
    eval_expr s (Eq (Var "q_size") (Var "q_capacity")) =!= 0

let post_lowest_freed (l_low : loc) : cond =
  fun s ->
    exists (old_score : value).
      s._3 == Ok /\
      points_to_empty (eval_expr s (Var "lowest")) s /\
      pre_realloc_branch l_low
        (s._1, override s._2 (eval_expr s (Var "lowest")) (Full old_score), Ok)

let post_dangling_lowest_write (l_low : loc) : cond =
  fun s ->
    s._3 == Er /\
    points_to_empty (eval_expr s (Var "lowest")) s /\
    post_lowest_freed l_low (s._1, s._2, Ok)

let proof_queue_push_realloc_path (l_low : loc)
  : isl_triple
      (is_ok (pre_lowest_in_full_queue l_low))
      queue_push_realloc_path
      (post_lowest_freed l_low) =
  let p_assume_raw =
    ISL_Assume #(pre_lowest_in_full_queue l_low)
      (Eq (Var "q_size") (Var "q_capacity"))
  in
  let p_assume =
    ISL_Consequence
      (pre_lowest_in_full_queue l_low)
      (pre_realloc_branch l_low)
      p_assume_raw
      ()
      ()
  in

  let p_free_raw = ISL_Free #(pre_realloc_branch l_low) (Var "lowest") in
  let p_free =
    ISL_Consequence
      (pre_realloc_branch l_low)
      (post_lowest_freed l_low)
      p_free_raw
      ()
      ()
  in

  let p_raw = ISL_Seq p_assume p_free in
  ISL_Consequence
    (pre_lowest_in_full_queue l_low)
    (post_lowest_freed l_low)
    p_raw
    ()
    ()

let proof_apply_catchup_bonus_realloc_bug (l_low : loc)
  : isl_triple
      (is_ok (pre_lowest_in_full_queue l_low))
      apply_catchup_bonus_realloc_path
      (post_dangling_lowest_write l_low) =
  let p_push = proof_queue_push_realloc_path l_low in
  let p_store_err =
    ISL_StoreEr #(post_lowest_freed l_low) (Var "lowest") (Var "avg")
  in
  let p_raw = ISL_Seq p_push p_store_err in
  ISL_Consequence
    (pre_lowest_in_full_queue l_low)
    (post_dangling_lowest_write l_low)
    p_raw
    ()
    ()

// Certificado: la escritura por puntero colgante es alcanzable.
// Testigo: cola llena (4/4), avg = 16, lowest = Loc 1 con la celda 1 liberada.

let st_tq = on var (fun y ->
  if y = "q_size" || y = "q_capacity" then Nat 4
  else if y = "avg" then Nat 16
  else if y = "lowest" then Loc 1
  else Nat 0)

let tq_reachable ()
  : Lemma (error_reachable (is_ok (pre_lowest_in_full_queue 1)) apply_catchup_bonus_realloc_path) =
  let hp_full = override (singleton_empty_heap 1) 1 (Full (Nat 5)) in
  assert (points_to 1 (Nat 5) (st_tq, hp_full, Ok));
  certify (proof_apply_catchup_bonus_realloc_bug 1) (st_tq, singleton_empty_heap 1, Er)
