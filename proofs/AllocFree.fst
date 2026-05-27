module AllocFree

open IncSepLogicOne

// Def del programa a verificar
(*
  x = alloc()
  free(x)
  *x = 1
*)

let post_alloc (s : state) : prop =
  exists (l : loc) (v : value). 
    s._3 == Ok /\ 
    s._1 "x" == Loc l /\ 
    l =!= 0 /\ 
    points_to l v s /\
    (exists x_old. emp (override s._1 "x" x_old, override s._2 l Empty, Ok))

let pre_free (s:state) : prop = 
  s._3 == Ok /\ post_alloc s

let post_free (s : state) : prop =
  exists (v : value). 
    s._3 == Ok /\
    points_to_empty (eval_expr s (Var "x")) s /\
    pre_free (s._1, override s._2 (eval_expr s (Var "x")) (Full v), Ok)

let pre_store (s : state) : prop =
  s._3 == Ok /\ post_free s

let post_uaf_err (s : state) : prop =
  s._3 == Er /\ 
  points_to_empty (eval_expr s (Var "x")) s /\
  pre_store (s._1, s._2, Ok)

let prog_uaf =
  (Alloc "x") `Seq`
  ((Free (Var "x")) `Seq`
  (Store (Var "x") (Const 1)))

let proof_uaf : isl_triple emp prog_uaf post_uaf_err =
  let p_alloc = ISL_Alloc1 #emp "x" in
  let p_free_raw = ISL_Free #pre_free (Var "x") in
  let p_store = ISL_StoreEr #pre_store (Var "x") (Const 1) in

  let p_free = ISL_Consequence pre_free post_free p_free_raw () () in

  let p_seq1 = ISL_Seq p_free p_store in
  let p_seq2 = ISL_Seq p_alloc p_seq1 in
  
  ISL_Consequence emp post_uaf_err p_seq2 () ()