#use "semantic-analyser.ml";;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "SOB_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (constant * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string*string) list -> (string * int) list

  (* This signature represents the idea of outputing assembly code as a string
     for a single AST', given the full constants and fvars tables. 
   *)
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;;



module Code_Gen : CODE_GEN = struct
  let make_consts_tbl asts = [(Sexpr Nil, (1, "MAKE_NIL"));(Void, (1, "MAKE_VOID"));(Sexpr(Bool false), (1, "MAKE_BOOL(0)"));(Sexpr(Bool true), (1, "MAKE_BOOL(1)"))];;

  let rec make_fvars ast freeVars=
    match ast with
    | Var'( VarFree (varName)) -> if(List.mem varName freeVars) then freeVars else freeVars@[varName]
    | Const' _  | Box' _ | BoxGet' _ -> freeVars
    | BoxSet'(var,value) -> make_fvars value freeVars
    | If' (test,dit,dif) -> List.fold_left (fun freeVars ast -> make_fvars ast freeVars) freeVars [test;dit;dif]
    | Seq' expList | Or' expList -> List.fold_left (fun freeVars ast -> make_fvars ast freeVars) freeVars expList
    | Set' (var,value) | Def' (var,value) -> List.fold_left (fun freeVars ast -> make_fvars ast freeVars) freeVars [var;value]
    | LambdaSimple' (params, body) -> make_fvars body freeVars
    | LambdaOpt'(params,param,body) -> make_fvars body freeVars
    | Applic' (operator, operands) | ApplicTP' (operator, operands) -> List.fold_left (fun freeVars ast -> make_fvars ast freeVars) freeVars (List.append [operator] operands)
    | _ -> freeVars

  let make_fvars_tbl asts prims = 
    let prims_list = List.mapi (fun index (prim,label) -> (prim,index*8)) prims in
    let next_index = ((List.length prims_list)-1) * 8 + 8 in
    let fvars = (List.fold_left (fun freeVars ast -> make_fvars ast freeVars) [] asts) in
    let fvars = List.mapi (fun index var-> (var,next_index+index*8)) fvars in  
    prims_list@fvars;;
  let generate consts fvars e = "";;
end;;



