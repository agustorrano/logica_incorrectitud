module PushBack

open IncSepLogicOne

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
    s._3 == Ok /\ s._1 ptr == Loc l_v /\
    (points_to l_v (Loc l_a) ** points_to l_a val_a) s

let post_load_x (ptr : var) (s : state) : prop =
  exists (l : loc) (v : value) (x_old : value).
    s._3 == Ok /\
    eval_expr (override s._1 "x" x_old, s._2, Ok) (Var ptr) == l /\
    points_to l v s /\
    s._1 "x" == v /\
    pre_client ptr (override s._1 "x" x_old, s._2, Ok)

let post_load_y (ptr : var) (s : state) : prop =
  exists (l : loc) (v : value) (x_old : value).
    s._3 == Ok /\
    eval_expr (override s._1 "y" x_old, s._2, Ok) (Var ptr) == l /\
    points_to l v s /\
    s._1 "y" == v /\
    post_load_x ptr (override s._1 "y" x_old, s._2, Ok)

let post_free_y (ptr : var) (s : state) : prop =
  exists (v : value).
    s._3 == Ok /\
    points_to_empty (eval_expr s (Var "y")) s /\
    post_load_y ptr (s._1, override s._2 (eval_expr s (Var "y")) (Full v), s._3)

let post_alloc_y (ptr : var) (s : state) : prop =
  exists (l : loc) (v : value).
    s._3 == Ok /\ s._1 "y" == Loc l /\ l =!= 0 /\
    points_to l v s /\
    (exists (x_old : value).
      post_free_y ptr (override s._1 "y" x_old, override s._2 l Empty, Ok))

let post_store_v (ptr : var) (s : state) : prop =
  s._3 == Ok /\
  points_to (eval_expr s (Var ptr)) (Nat (eval_expr s (Var "y"))) s /\
  (exists (v_old : value).
    post_alloc_y ptr (s._1, override s._2 (eval_expr s (Var ptr)) (Full v_old), Ok))

let post_err (ptr : var) (s : state) : prop =
  s._3 == Er /\
  points_to_empty (eval_expr s (Var "x")) s /\
  post_store_v ptr (s._1, s._2, Ok)

let proof_client (ptr : var) : isl_triple (pre_client ptr) (client ptr) (post_err ptr) =
  
  let p_load_x_raw = ISL_Load #(pre_client ptr) "x" (Var ptr) in
  let p_load_x = ISL_Consequence (pre_client ptr) (post_load_x ptr) p_load_x_raw () () in

  let pre_y = fun (s : state) -> s._3 == Ok /\ post_load_x ptr s in
  let p_load_y_raw = ISL_Load #pre_y "y" (Var ptr) in
  let p_load_y = ISL_Consequence pre_y (post_load_y ptr) p_load_y_raw () () in

  let p_free_y = ISL_Free (Var "y") in
  let p_alloc_y = ISL_Alloc1 "y" in
  let p_store_v = ISL_Store (Var ptr) (Var "y") in

  let p_seq_pb3 = ISL_Seq p_alloc_y p_store_v in
  let p_seq_pb2 = ISL_Seq p_free_y p_seq_pb3 in
  let p_seq_pb1 = ISL_Seq p_load_y p_seq_pb2 in

  let p_push_back_raw = ISL_ChoiceL p_seq_pb1 in
  let p_push_back = ISL_Consequence pre_y (post_store_v ptr) p_push_back_raw () () in

  let pre_err_step = fun (s : state) -> s._3 == Ok /\ post_store_v ptr s in
  let p_store_err_raw = ISL_StoreEr #pre_err_step (Var "x") (Const 88) in
  let p_store_err = ISL_Consequence pre_err_step (post_err ptr) p_store_err_raw () () in

  let p_client_seq2 = ISL_Seq p_push_back p_store_err in
  
  let p_client_raw : isl_triple (pre_client ptr) (client ptr) 
    (fun s -> post_err ptr s \/ (s._3 == Er /\ post_store_v ptr s) \/ (s._3 == Er /\ post_load_x ptr s)) = 
    ISL_Seq p_load_x p_client_seq2 
  in

  ISL_Consequence (pre_client ptr) (post_err ptr) p_client_raw () ()