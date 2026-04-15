module ISLPrograms

open IncSepLogic

(*
n := 1000000;
i, j := 0;
while (i <= n){
  i++;
  if (random()) j++;
}
assert  (j != n);
*)

let ( ||| ) = Choice

let enot (e : expr) : expr = Minus (Const 1) e
let ge (x y : expr) : expr = enot (Lt x y)

// n := 1000000; i := 0; j := 0;
unfold let init_vars = 
  Assign "n" (Const 1000000) `Seq`
  Assign "i" (Const 0) `Seq`
  Assign "j" (Const 0)

// el cuerpo del while
let loop_body =
  Assume (Lt (Var "i") (Var "n")) `Seq`
  Assign "i" (Plus (Var "i") (Const 1)) `Seq`
  (Assign "j" (Plus (Var "j") (Const 1)) ||| Skip)

let assert_stmt =
  Seq (Assume (Eq (Var "j") (Var "n"))) Error |||
  Assume (enot (Eq (Var "j") (Var "n")))

unfold let prog1 =
  init_vars `Seq`
  Kleene loop_body `Seq`
  Assume (ge (Var "i") (Var "n")) `Seq`
  assert_stmt


(*
  {true}
  x = alloc()
  *x = 1
  {er: x=NULL}
*)
(*
  x = alloc()
  free(x)
*)
