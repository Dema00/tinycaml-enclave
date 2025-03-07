open Ast

(*
    Return true if l1 is sublist of l2.
*)
let rec sublist l1 l2 =
  match l1 with
  | [] -> true
  | e :: l -> if List.mem e l2 then sublist l l2 else false
;;

(*
  Given a list, it searches recursively the security level.
*)
let rec sec_lvl_from_list list el base_val =
  match list with
  | h :: t -> if h = el then 2 else sec_lvl_from_list t el base_val
  | [] -> base_val
;;

let pop_list l =
  match l with
  | _ :: t -> t
  | [] -> []
;;

(* It prints the value associated to type a. *)
let print_value a =
    match a with
    | Int(i) -> print_int i; print_endline " ";
    | REnclave(_) -> print_endline "enclave";
    | Closure(_) -> print_endline "closure";
    | Str(s) -> print_endline "aa"; print_endline s;
    | _ -> failwith "not supported"
;;