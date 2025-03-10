(*
  Environment Representation.
*)

(* Variable identifiers are strings *)
type ide = string

(*
  An environment is a map from identifier to a value (what the identifier is bound to).
  For simplicity we represent the environment as an association list, i.e., a list of pair (identifier, data).
*)
type 'v env =  (ide * 'v) list

(*
  Given an environment {env} and an identifier {x} it returns the data {x} is bound to.
  If there is no binding, it raises an exception.
*)
let rec lookup env (x : ide) =
  match env with
    | [] -> failwith (x ^ " not found") 
    | (y, v) :: r -> if x = y then v else lookup r x


(*
  Given an environment {env} and an identifier {x} it returns the data {x} is bound to.
  If there is no binding, it returns None.
*)
let rec option_lookup env (x : ide) =
  match env with
    | [] -> None
    | (y, v) :: r -> if x = y then Some(v) else option_lookup r x