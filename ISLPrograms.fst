module ISLPrograms

open IncSepLogic

// n := 1000000; i := 0; j := 0;
unfold let init_vars = 
  Seq (Assign "n" (Const 1000000))
      (Seq (Assign "i" (Const 0)) (Assign "j" (Const 0)))

// el cuerpo del while
let loop_body =
  Seq (Assume (Lt (Var "i") (Var "n")))
      (Seq (Assign "i" (Plus (Var "i") (Const 1)))
           (Choice Skip (Assign "j" (Plus (Var "j") (Const 1)))))

let assert_stmt =
  Choice (Seq (Assume (Eq (Var "j") (Var "n"))) Error)
         (Choice (Seq (Assume (Lt (Var "j") (Var "n"))) Skip)
                 (Seq (Assume (Gt (Var "j") (Var "n"))) Skip))

unfold let prog1 =
  Seq init_vars
      (Seq (Kleene loop_body)
           (Seq (Assume (Eq (Var "i") (Var "n"))) assert_stmt))
