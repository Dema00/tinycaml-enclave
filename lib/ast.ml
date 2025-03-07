(*
   Abstract Syntax Tree Representation.
*)
open Env


(*
\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\  Type of execution scope.  \
\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
*)
type trust = 
   (* It denotes that the code is executed inside an Enclave. *)
   | EnclaveLvl
   
   (* It denotes that the code is executed in a trusted block. *)
   | Trusted

   (* It denotes that the code is executed in an untrusted block. *)
   | Untrusted

   
(*
   \\\\\\\\\\\\\\\\\\\\\\\\\\\
   \  Lattice representation  \
   \\\\\\\\\\\\\\\\\\\\\\\\\\\\
*)
type conf =
   (* High level (CONFIDENTIAL) *)
   | H

   (* Low level (NOT CONFIDENTIAL) *)
   | L


(*
   \\\\\\\\\\\\\\\\\\\\\\\
   \  Syntax Tree Type    \
   \\\\\\\\\\\\\\\\\\\\\\\\
*)
type expr =
   | CstI of int
   | CstB of bool
   | CstS of string
   | Var of ide
   | Let of ide * conf * expr * expr
   | Prim of ide * expr * expr
   | If of expr * expr * expr
   | Fun of ide * expr
   | Call of expr * expr
   | Abort of string
   (* Utility function *)
   | Print of expr * expr

   (* Enclave is composed of:
      1. ide   : the identifier of the enclave
      2. expr  : the contents of the enclave
      3. expr  : the body of the enclave
   *)
   | Enclave of ide * expr * expr

   (* GatewayCall is composed of:
      1. ide  : the enclave identifier
      2. ide  : the ide of gateway of the enclave
      3. expr  : the argument of the gateway
   *)
   | GatewayCall of ide * ide * expr

   (* Gateway is composed of:
      1. ide  : the name of the function that is going to be designated as gateway
      2. expr  : the body of the gateway
   *)
   | Gateway of ide * expr

   (* EndEnclave is the last expression in the enclave declaration *)
   | EndEnclave

   (* Include is composed of:
      1. trust : the scope level
      2. ide: the identifier of code.
      3. expr : the code to be executed as "external code"
      4. expr : the body of the include.
   *)
   | Include of trust * ide * expr * expr

   (* EndInclude is the last expression in the Include declaration *)
   | EndInclude

   (* Exec is composed of: 
      1. ide : the identifier of external code.
      2. expr : the body of execution.
   *)
   | Exec of ide * expr
   | Declassify of ide
   | Empty
;;


(*
   \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
   \  Enclave Record Definition    \
   \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\

   It is the Runtime Structure for representing an Enclave.
*)
type 'v enclaveRecord = {
   (* Enclave Environment. *)
   enEnv : 'v env;

   (* Trusted Gateways *)
   enGtws : 'v env;

   (* Untrusted Gateways *)
   enUntGtws: 'v env

};;



(*
   \\\\\\\\\\\\\\\\\\\
   \  Runtime Values  \
   \\\\\\\\\\\\\\\\\\\\

   Definition of runtime values: i.e. values returned by interpreter.
*)
type value = 
   (* Basic return values. *)
   | Str of string
   | Int of int
   | RGateway of value ref
   | Closure of ide * expr  * value env

   (* Runtime Enclave. *)
   | REnclave of value enclaveRecord

   (* Runtime Include. 
      1. trust : the scope of the code
      2. expr : the code to be executed.   
   *)
   | RInclude of trust * expr

   (* Execution Termination. *)
   | ExecTermination of value env
;;