open Enclave.Ast
open Enclave.Interpreter
open Enclave.Sec


(*

\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\         TEST CASE 1       \
\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\

enclave myenc
  let secret psw = 5
  let checkPsw guess =
    psw = guess
  
  gateway checkPsw
end

let res = myenc checkPsw 5
print res

include untrusted ext
  let a = myenc checkPsw 5
exec ext
a
*)
let test_inc =
  (
    Enclave
      (
        "myenc",
        (
          Let (
            "psw",
            L,
            (CstS "abc"),
            (
              Let
                (
                  "checkPsw",
                  L,
                  (
                    Fun
                      (
                        "guess",
                        ((Prim("cmp",(Var "psw"),(Var "guess"))))
                      )
                  ),
                  Gateway
                    (
                      "checkPsw",
                      EndEnclave
                    )
                )
            )
          )
        ),
        Include
        (
          Untrusted,
          "ext",
          Let
            (
              "a",
              L,
              GatewayCall
                (
                  "myenc",
                  "checkPsw",
                  (CstS "abc")
                ),
              EndInclude
            ),
          (
            Let
              (
                "res",
                L,
                (
                  GatewayCall
                    (
                      "myenc",
                      "checkPsw",
                      (CstS "abc")
                    )
                ),
                (
                  Print
                    (
                      (Var "res"),
                      Exec
                        (
                          "ext",
                          (Var "a")
                        )
                    )
                )
              )
          )
        )
      )
  )

(*

\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\         TEST CASE 2       \
\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\

enclave myenc
  let secret psw = 5
  let checkPsw guess =
    if psw = guess then
      true
  
  gateway checkPsw
end

let res = myenc checkPsw 5
print res

include untrusted ext
  let a = myenc checkPsw 5
exec ext
a
*)
let test_inc_if =
  (
    Enclave
      (
        "myenc",
        (
          Let (
            "psw",
            H,
            (CstS "abc"),
            (
              Let
                (
                  "checkPsw",
                  L,
                  (
                    Fun
                      (
                        "guess",
                        (
                          If
                          (
                            (Prim("cmp",(Var "psw"),(Var "guess"))),
                            (CstB true),
                            (CstB false)
                          )
                        )
                      )
                  ),
                  Gateway
                    (
                      "checkPsw",
                      EndEnclave
                    )
                )
            )
          )
        ),
        Include
        (
          Untrusted,
          "ext",
          Let
            (
              "a",
              L,
              (
                Declassify "res"
              ),
              EndInclude
            ),
          (
            Let
              (
                "res",
                H,
                (
                  GatewayCall
                    (
                      "myenc",
                      "checkPsw",
                      (CstS "abc")
                    )
                ),
                (
                  
                    Exec
                      (
                        "ext",
                        Print 
                        (
                          (Var "a"),
                          (Var "a")
                        )
                      )
                  
                )
              )
          )
        )
      )
  )

(*
\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\         TEST CASE 3       \
\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\

H let a = 1 in
L let b = 0 in

let H c = (
  if a = b then
    0
    else
    1
)

*)

let test_if =
  (
    Let (
      "a",
      H,
      (CstI 1),
      (
        Let (
          "b",
          L,
          (CstI 2),
          (
            Let (
              "c",
              H,
              (
                If (
                  (Prim("=",(Var "a"),(Var "b"))),
                  (Var "a"),
                  (CstI 1)
                )
              ),
              (Var "c")
            )
          )
        )
      )

    )
  )


(*
\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\         TEST CASE 4       \
\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\

include untrusted c =
  let L d = 1

exec c;
*)

let test_inc_unt =
  (
    Include(
      Untrusted,
      "c",
      (
        Let (
          "d",
          L,
          (CstI 1),
          EndInclude
        )
      ),
      (
        Exec("c",(CstI 1))
      )
    )
  )

let test_fun test res =
  print_endline "----------- running a test -----------";
  let env = Hashtbl.create 10 in
  scheck test env L [] Trusted |> ignore; (* static checking *)
  match eval test [] Trusted = res with
  | true -> print_endline "test successful";
  | false -> print_endline "test failed"
;;
let test_list = test_inc_unt::test_if::test_inc::test_inc_if::[] in
let res_list  = (Int 1 )::(Int 1 )::(Int 1 )::(Int 1 )::[] in

List.iter2 test_fun test_list res_list

(*
let a = (
  enclave myenc
    let secret a = 2
  end
)
*)