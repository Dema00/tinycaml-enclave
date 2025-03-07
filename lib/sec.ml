open Ast
open Env

open Hashtbl

(* Security Policy Implementation. *)
let join (e1: conf) (e2: conf) =
  match (e1, e2) with
  | (H, H) -> H
  | (L, L) -> L
  | (H, L) -> H
  | (L, H) -> H
(* 
   @OPTIMIZATION: can be replaced by 
    | (L, L) -> L 
    | _ -> H
    but it is less explicit.
*)

(* l1 <= l2 for Hi-Lo type system*)

let ( <:= ) l1 l2 =
  match (l1, l2) with
  | (H, L) -> false
  | _ -> true

(* l1 >= l2 for Hi-Lo type system*)
let ( >:= ) l1 l2 =
  match (l1, l2) with
  | (L, H) -> false
  | _ -> true

let ( <: ) l1 l2 =
  not (l1 >:= l2)

let ( >: ) l1 l2 =
  not (l1 <:= l2)

let sec_insert (env: (ide,conf) t) ide slvl =
  match Hashtbl.find_opt env ide with
  | Some(c_slvl) -> (
    Hashtbl.replace env ide (join c_slvl slvl)
  )
  | None -> Hashtbl.replace env ide slvl

let insert (env: (ide,conf) t) ide slvl =
  Hashtbl.replace env ide slvl

let rec get_gtw_names exp gtws=
  match exp with
  | Gateway (n,e) -> (
    get_gtw_names e ((n)::gtws);
  )
  | Let (_,_,_,b) -> (
    get_gtw_names b gtws
  )
  | _ -> gtws

let print_conf conf =
  match conf with
  | H -> print_string "H"
  | L -> print_string "L"


let rec get_gtw_slvls gtw_names (map: (ide, conf) Hashtbl.t) acc n_e =
  match gtw_names with
  | h :: t -> let nAcc = (n_e ^ h, (Hashtbl.find map h)) :: acc in get_gtw_slvls t map nAcc n_e
  | [] -> acc

(*
   \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
   \  STATIC CHECKING FOR HW 1    \
   \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
*)

(* Static checking method for gateways exposed to the trusted environment *)
let rec tgtws_sec ast (env: (ide,conf) t) (slvl:conf) =
  match ast with
  | CstI(_) -> slvl
  | CstB(_) -> slvl
  | CstS(_) -> slvl
  | Var(x) -> Hashtbl.find env x
  | Let(n, c, a, b) -> (
      Hashtbl.replace env n c;
      let arg_slvl = (tgtws_sec a env c) in
      let body_slvl = (tgtws_sec b env slvl) in
      
      Hashtbl.replace env n (join arg_slvl (Hashtbl.find env n));
      body_slvl
    )
  | If(_, e1, e2) -> (
        join (tgtws_sec e1 env slvl) (tgtws_sec e2 env slvl)
    )
  | Prim (_, _, _) -> slvl
  | Call (f, a) -> (
        join (tgtws_sec f env slvl) (tgtws_sec a env slvl)
    )
  | GatewayCall (_, _, a) -> tgtws_sec a env slvl
  | Gateway (n, b) -> (
      Hashtbl.replace env n slvl;
      (tgtws_sec b env slvl)
    )
  | EndEnclave -> slvl
  | Fun(a, c) -> (
        Hashtbl.replace env a slvl;
        (tgtws_sec c env slvl))
  | Enclave(_, _, _) -> (
        failwith "an enclave should not be inside of an enclave"
    )
  | _ -> failwith "an illegal expression was encountered during the trusted static checking."

(* Static checking method for gateways exposed to the untrusted environment *)
let rec ugtws_sec ast (env: (ide,conf) t) (slvl: conf) =
  match ast with
  | CstI(_) -> slvl
  | CstB(_) -> slvl
  | CstS(_) -> slvl
  | Var(x) -> Hashtbl.find env x
  | Let(n, c, a, b) -> (
      Hashtbl.replace env n c;
      let arg_slvl = (ugtws_sec a env c) in
      let body_slvl = (ugtws_sec b env slvl) in
      
      Hashtbl.replace env n (join arg_slvl (Hashtbl.find env n));
      body_slvl
    )
  | If(g, e1, e2) -> (
        (join
          (ugtws_sec g env slvl)
          (join (ugtws_sec e1 env slvl) (ugtws_sec e2 env slvl))
        )
      )
  | Prim (_, e1, e2) -> join (ugtws_sec e1 env slvl) (ugtws_sec e2 env slvl)
  | Call (f, a) -> (
        join (ugtws_sec f env slvl) (ugtws_sec a env slvl)
    )
  | GatewayCall (_, _, a) -> (ugtws_sec a env slvl)
  | Gateway (_, b) -> (ugtws_sec b env slvl)
  | EndEnclave -> slvl
  | Fun(a, c) -> (
        Hashtbl.replace env a slvl;
        (ugtws_sec c env slvl)
        )
  | Enclave(_, _, _) -> (
      failwith "an enclave should not be inside of an enclave"
    )
  | _ -> failwith "an illegal expression was encountered during the untrusted static checking."

  (*
   \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
   \  STATIC CHECKING FOR HW 2     \
   \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
*)

let rec insert_gtws env x = 
  match x with
  | [] -> ()
  | (ide, slvl)::t -> insert env ide slvl; insert_gtws env t

let rec scheck ast (env: (ide,conf) t) (slvl:conf) (inc: (expr * conf) env) (tlvl: trust)=
  match ast with
  | CstI(_) -> slvl
  | CstB(_) -> slvl
  | CstS(_) -> slvl
  | Var(x) -> Hashtbl.find env x
  | Let(n, c, a, b) -> (

      let arg_slvl = scheck a env slvl inc tlvl in
      if c <: (join arg_slvl slvl) then
        failwith "Static check: Illegal variable declaration"
      ;

      if tlvl = Untrusted then

        if c >: H then
          failwith "Static check: can't declare a confidential variable in an untrusted environment"
      ;
      sec_insert env n c;
      scheck b env slvl inc tlvl
    )
  | If(g, e1, e2) -> (
      let g_slvl = scheck g env slvl inc tlvl in
      let e1_slvl = scheck e1 env slvl inc tlvl in
      let e2_slvl = scheck e2 env slvl inc tlvl in
      let if_slvl = join g_slvl slvl in
      
      if if_slvl >: (join e1_slvl e2_slvl) then
        failwith "Static check: The security level of the guard is higher than the one of the branches"
      ;
      join (join if_slvl e1_slvl) e2_slvl
    )
  | Fun(_, c) -> (
      scheck c env slvl inc tlvl
    )
  | Call (f, a) -> (
      join (scheck f env slvl inc tlvl) (scheck a env slvl inc tlvl)
    )
  | Print (a,b) -> (
    if (scheck a env slvl inc tlvl) >:= H then
      failwith "Static check: Can't print confidential information"
    ;
    scheck b env slvl inc tlvl
  )
  | Enclave (n,e,b) -> (
    let new_env = Hashtbl.create 10 in
    ugtws_sec e new_env L |> ignore;
    let gtws = get_gtw_names e [] in
    let gtws_slvls = get_gtw_slvls gtws new_env [] n in
    insert_gtws env gtws_slvls;
    scheck b env slvl inc tlvl)

  | GatewayCall (e_n,n,_) -> (
    Hashtbl.find env (e_n ^ n)
  )
  | Gateway(_) -> failwith "Static chek: Gateway in an illegal position"
  | EndEnclave -> failwith "Static chek: EndEnclave in an illegal position"
  | EndInclude -> slvl
  | Include (t,n,e,b) -> 
    if b = Empty then
      slvl
    else
    let itlvl = match t with
      | Untrusted -> L
      | _ -> H
    in
    let new_inc = (n,(e,itlvl))::inc in
    
    scheck b env slvl new_inc tlvl
  | Declassify (_) -> (
    L
  )
  | Prim(_) -> slvl
  | Exec (n,b) -> 
    let e, itlvl = lookup inc n in
    scheck e env itlvl inc Untrusted |> ignore;

    scheck b env slvl inc tlvl
  | Empty -> slvl
  | Abort(_) -> slvl