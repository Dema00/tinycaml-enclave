open Ast
open Env
open Rts
open Utils

(*
\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\  Interpreter MAIN Function \
\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
*)

let rec eval (e : expr) (env: value env) (slvl: trust)=
    match e with
    | Abort msg -> failwith msg
    | CstI i -> Int i
    | CstB b -> Int (if b then 1 else 0)
    | CstS s -> Str s
    
    (* Lookup variable x inside current environment. *)
    | Var x -> (
        lookup env x
    )

    (*
        Let implementation.
        1. x : the identifier of let
        2. conf: lattice
        3. eRhs : the value to bind to x.
        4. letBody: "in" of let.
    *)
    | Let (x, conf, eRhs, letBody) -> (
        if slvl = Untrusted && conf = H then
            (* In untrusted block it's not allowed to declare a let with H confidentiality.*)
            failwith "Can't declare a secret in an untrusted environment"
        else if option_lookup env x != None && slvl = Untrusted then
            failwith "Can't shadow an existing variable from untrusted code"
        else
            (* Execute the let binding. *)
            let xVal = eval eRhs env slvl in
            let letEnv = (x, xVal) :: env in
            eval letBody letEnv slvl
    )

    (* Basic arithmetic operations *)
    | Prim (ope, e1, e2) -> (
        let v1 = eval e1 env slvl in
        let v2 = eval e2 env slvl in
        match (ope, v1, v2) with
        | "*", Int i1, Int i2 -> Int (i1 * i2)
        | "+", Int i1, Int i2 -> Int (i1 + i2)
        | "-", Int i1, Int i2 -> Int (i1 - i2)
        | "=", Int i1, Int i2 -> Int (if i1 = i2 then 1 else 0)
        | "<", Int i1, Int i2 -> Int (if i1 < i2 then 1 else 0)
        | "cmp", Str s1, Str s2 -> Int (if (String.compare s1 s2) = 0 then 1 else 0) 
        | _ -> failwith "unknown primitive or wrong type"
        )

    (* Basic IF logic implementation *)
    | If (e1, e2, e3) -> (
        match eval e1 env slvl with
        | Int 0 -> eval e3 env slvl
        | Int _ -> eval e2 env slvl
        | _ -> failwith "eval if"
        )
    
    (* Fun declaration, it returns a closure using current environment. *)
    | Fun (x, fBody) -> (
        Closure (x, fBody, env)
    )

    (* Call the function. *)
    | Call (eFun, eArg) -> (
        let fClosure = eval eFun env slvl in
        match fClosure with
            | Closure (x, fBody, fDeclEnv) ->
                (* xVal is evaluated in the current stack *)
                let xVal = eval eArg env slvl in
                let fBodyEnv = (x, xVal) :: fDeclEnv in
                (* fBody is evaluated in the updated stack *)
                eval fBody fBodyEnv slvl
            | _ -> failwith "eval Call: not a function"
    )

    (* Gateway declaration. It takes: 
        1. name : the name
        2. body : the body (continuation of code)
    It searches the given identifier inside the current environment.
    It checks if it is a closure and than it eval the body.
    *)
    | Gateway(name, body) -> (
        let gtw = lookup env name in
        match gtw with
        | Closure(_) -> (
            let gtw_ref = RGateway (ref gtw) in
                eval body ((name, gtw_ref) :: env) slvl
            )
        | _ -> failwith ("The gateway " ^ " is not a function")
        
    )

    (*
        Call a gateway!
        It takes: 
            1. Enclave name
            2. The name of the gateway
            3. The argument.
    *)
    | GatewayCall(enclave_name, gateway, arg) -> (
        (* First evaluate the argument. *)
        let eArg = eval arg env slvl in
        (* Lookup the enclave inside current environment. *)
        let eEnc = lookup env enclave_name in
        (* Perform security checks. *)
        match eEnc with
        | REnclave(record) -> (
            (* The enclave has been found.*)
            match slvl with
            | Untrusted -> (
                (* we are inside an untrusted block *)
                let eGtw = option_lookup record.enUntGtws gateway in
                match eGtw with
                | Some(reference) -> (
                    (* gateway has been found! *)
                    match !(get_reference_inner reference) with
                        (* It access to the value pointed to the reference and it checks if it is a closure. *)
                        | Closure(argName, gtwBody, gtwEnv) -> eval gtwBody ((argName, eArg) :: gtwEnv) slvl
                        | _ -> failwith "Not a closure"
                    )
                | None -> failwith (gateway ^ " is not a gateway accessible from untrusted code or wasn't declared")
            )
            | _ -> (
                (* we are inside a trusted environment or inside an environment. *)
                let eGtw = lookup record.enGtws gateway in
                match !(get_reference_inner eGtw) with
                    (* Access to reference and execute the function, if it's a closure. *)
                    | Closure(argName, gtwBody, gtwEnv) -> eval gtwBody ((argName, eArg)::gtwEnv) slvl
                    | _ -> failwith "not a closure"
            )
        )
        | _ -> failwith "Not an enclave"
    )

    (* crea nuovo Frame e pushalo nell'environment
     e esegui eval expr nuovo_env
     
     *)
    | Enclave (iden, contents, encBody) -> (
        if (option_lookup env iden) != None then
            failwith (iden ^ " is already declared as an enclave")
        else if slvl = EnclaveLvl then
            failwith ("can't declare an enclave inside another one")
        else if slvl = Untrusted then
            failwith ("can't declare an enclave inside of untrusted code")
        else
            let result = eval contents [] EnclaveLvl in
            match result with
            | ExecTermination(enEnv) -> (
                let enGtws = get_tgtws contents enEnv in
                let enUntGtws = get_ugtws contents enEnv in
                let rEnclave = REnclave {enEnv = enEnv; enGtws = enGtws; enUntGtws = enUntGtws} in
                if String.length iden = 0 && encBody = Empty then
                rEnclave
                    else
                eval encBody ((iden,rEnclave)::env) slvl
            )
            | _ -> failwith "enclave not declared correctly"

    )

    | EndEnclave -> (
        ExecTermination env
    )

    | Include (trust, name, code, incBody) -> (
        if slvl = EnclaveLvl then
            failwith "can't include external code inside of an enclave"
        else
        let rInclude = RInclude(trust,code) in
        if String.length name = 0 && incBody = Empty then
            rInclude
        else
        eval incBody ((name, rInclude)::env) slvl
    )

    | Exec (incName, exeBody) -> (
        let inc = lookup env incName in
        match inc with
        | RInclude(trust, code) -> (
            match trust with
            | Untrusted -> (
                match (eval code env Untrusted) with
                    | ExecTermination(exec_env) -> eval exeBody exec_env Trusted
                    | _ -> failwith "not terminated correctly"
                )
            | Trusted -> (
                match (eval code env Trusted) with
                    | ExecTermination(exec_env) -> eval exeBody exec_env Trusted
                    | _ -> failwith "not terminated correctly"
                )
            | EnclaveLvl -> failwith "can't exec code inside of an enclave"
        )
        | _ -> failwith "include not found"
    )

    | EndInclude -> ExecTermination env

    | Print(expr, body) -> (
        if slvl = EnclaveLvl then
            failwith "can't print inside of an enclave"
        else
        let eExpr = eval expr env slvl in
        print_value eExpr;
        eval body env slvl
    )

    | Declassify (ide) -> lookup env ide

    | Empty -> failwith "no further operations in the progam"
