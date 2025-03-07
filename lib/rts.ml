open Ast
open Sec
open Env
(*open Printf*)

(* Given a value it returns the reference associated to the value. *)
let get_reference_inner reference =
  match reference with
  | RGateway(pointed) -> pointed
  | _ -> failwith "Not a reference"

(* Given an environment and a list of values, it searches the gateways inside. *)
let rec lookup_gtws env name_acc gtw_acc =
  match env with
  | (n, v) :: t -> (
      match v with
      | RGateway(_) -> (n :: name_acc,(n, v)::gtw_acc)
      | _ -> lookup_gtws t name_acc gtw_acc
      )
  | [] -> (name_acc, gtw_acc)

let filter_conf = fun tup ->
  let (_, b) = tup in
  match b with
  | H -> false
  | L -> true

let rec get_gtw_slvls gtw_names (map: (ide, conf) Hashtbl.t) acc=
  match gtw_names with
  | h :: t -> let nAcc = (h, (Hashtbl.find map h)) :: acc in get_gtw_slvls t map nAcc
  | [] -> acc

(* 
  Get Trusted Gateway.
  Given an expresion ast, and an enclaveEnvironment it searches
*)
let get_tgtws ast enEnv =
  let checkEnv = Hashtbl.create 10 in (*create hashtbl*)
  let _ = tgtws_sec ast checkEnv L in (*static check, fill hashtbl*)
  let gtw_names,binds = lookup_gtws enEnv [] [] in (*get gtw names, refs*)
  let gtws_slvls = get_gtw_slvls gtw_names checkEnv [] in (*get (n,slvl)list of gtws from hashtbl*)
  (*print_int (List.length gtws_slvls);
  List.iter (printf "gtws %s \n") (gtw_names);
  List.iter (printf " val of gtw %s \n") (List.map (fun (a,b) -> print_conf b;a) gtws_slvls);*)
  let filtered = List.filter (filter_conf) gtws_slvls in
  (* List.iter (printf "second %s \n") (List.map (fun (a,_) -> a) filtered); *)
  if List.length filtered = List.length gtw_names then
    binds
  else
    failwith "a gateway can't return or be a secret"


let rec link_gtws name_list enEnv (acc: (ide * value) list) =
  match name_list with
  | (n, _) :: t -> link_gtws t enEnv ((n, (lookup enEnv n)) :: acc)
  | [] -> acc

let get_ugtws ast (enEnv: (ide * value) list) =
  let checkEnv = Hashtbl.create 10 in (*create hashtbl*)
  let _ = ugtws_sec ast checkEnv L in (*static check, fill hashtbl*)
  let gtw_names, _ = lookup_gtws enEnv [] [] in (*get gtw names, refs*)
  let gtws_slvls = get_gtw_slvls gtw_names checkEnv [] in (*get (n,slvl)list of gtws from hashtbl*)
  (*print_int (List.length gtws_slvls);
  List.iter (printf "gtws %s \n") (gtw_names);
  List.iter (printf " val of gtw %s \n") (List.map (fun (a,b) -> print_conf b;a) gtws_slvls);*)
  let filtered = List.filter (filter_conf) gtws_slvls in
  link_gtws filtered enEnv []
  (*List.iter (printf "second %s \n") (List.map (fun (a,_) -> a) filtered);*)