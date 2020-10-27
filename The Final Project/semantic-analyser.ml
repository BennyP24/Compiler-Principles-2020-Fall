#use "tag-parser.ml";;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                            (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
    | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
    | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
    (List.for_all2 String.equal vars1 vars2) &&
    (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
    (String.equal var1 var2) &&
    (List.for_all2 String.equal vars1 vars2) &&
    (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
    (expr'_eq e1 e2) &&
    (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;


exception X_syntax_error;;

module type SEMANTICS = sig
   val run_semantics : expr -> expr'
   val annotate_lexical_addresses : expr -> expr'
   val annotate_tail_calls : expr' -> expr'
   val box_set : expr' -> expr'
   end;;

   module Semantics : SEMANTICS = struct

let counterRef = ref 0;;

let reset_ref counter = counter:= 0;;

let rec check_read_occurence element body counter = 
  let constant = -1 in
  match body with 
  | Const' _ -> []
  | Var' var -> 
    if ((match var with 
        | VarFree(v) -> v=element 
        | VarParam(v,_) -> v=element
        | VarBound(v,_,_) -> v=element) = true) then [constant] else []
  | If' (test, dit, dif) -> (check_read_occurence element test counter)@(check_read_occurence element dit counter)@(check_read_occurence element dif counter)
  | Seq' exprs -> List.fold_left (fun acc seqElement -> (check_read_occurence element seqElement counter)@acc) [] exprs
  | Or' exprs -> List.fold_left (fun acc orElement -> (check_read_occurence element orElement counter)@acc) [] exprs
  | Set' (varName, value) -> (check_read_occurence element value counter)
  | Def' (varName, value) -> (check_read_occurence element value counter)
  | LambdaSimple' (params, newBody) -> 
    let counter2 = incr counter; !counter in
    if(List.mem element params) then [] else
      let check_read_occurence_body = check_read_occurence element newBody counter in
      (match List.length check_read_occurence_body with
       | 0 -> []
       | _ -> [counter2])
  | LambdaOpt' (params, param, newBody) -> 
    let counter2 = incr counter; !counter in
    if(List.mem element (params@[param])) then [] else
      let check_read_occurence_body = check_read_occurence element newBody counter in
      (match List.length check_read_occurence_body with
       | 0 -> []
       | _ -> [counter2])
  | Applic' (operator, operands) -> (check_read_occurence element operator counter) @ (List.fold_left (fun acc operandElement -> (check_read_occurence element operandElement counter)@acc) [] operands)
  | ApplicTP' (operator, operands) -> (check_read_occurence element operator counter) @ (List.fold_left (fun acc operandElement -> (check_read_occurence element operandElement counter)@acc) [] operands)
  | _ -> raise X_syntax_error;;

let rec check_write_occurence element body counter = 
  let constant = -1 in
  match body with 
  | Const' _ -> []
  | Var' var -> []
  | If' (test, dit, dif) -> (check_write_occurence element test counter)@(check_write_occurence element dit counter)@(check_write_occurence element dif counter)
  | Seq' exprs -> List.fold_left (fun acc seqElement -> (check_write_occurence element seqElement counter)@acc) [] exprs
  | Or' exprs -> List.fold_left (fun acc orElement -> (check_write_occurence element orElement counter)@acc) [] exprs
  | Set' (Var' varName, value) ->    
    if ((match varName with 
        | VarFree(v) -> v=element 
        | VarParam(v,_) -> v=element
        | VarBound(v,_,_) -> v=element) = true) then [constant]@(check_write_occurence element value counter)
    else (check_write_occurence element value counter)
  | Def' (varName, value) -> (check_write_occurence element value counter)
  | LambdaSimple' (params, newBody) -> 
    let counter2 = incr counter; !counter in
    if(List.mem element params) then [] else
      let check_write_occurence_body = check_write_occurence element newBody counter in
      (match List.length check_write_occurence_body with
       | 0 -> []
       | _ -> [counter2])
  | LambdaOpt' (params, param, newBody) -> 
    let counter2 = incr counter; !counter in
    if(List.mem element (params@[param])) then [] else
      let check_write_occurence_body = check_read_occurence element newBody counter in
      (match List.length check_write_occurence_body with
       | 0 -> []
       | _ -> [counter2])
  | Applic' (operator, operands) -> (check_write_occurence element operator counter) @ (List.fold_left (fun acc operandElement -> (check_write_occurence element operandElement counter)@acc) [] operands)
  | ApplicTP' (operator, operands) -> (check_write_occurence element operator counter) @ (List.fold_left (fun acc operandElement -> (check_write_occurence element operandElement counter)@acc) [] operands)
  | _ -> raise X_syntax_error;;


let set_box_list params = 
  List.map (fun param -> Set'(Var'(param), Box'(param))) params;;

let rec box_params var body = 
  let counter = ref 0 in
  let read_occurences = (check_read_occurence var body counter) in
  let read_occurences_length = List.length read_occurences in
  let counter = ref 0 in
  let write_occurences = (check_write_occurence var body counter) in
  let write_occurences_length = List.length write_occurences in

  match read_occurences_length,write_occurences_length with
  | 0, _ | _,0 -> false
  | _,_ ->
    let cartesian = List.concat (List.map (fun element-> List.map (fun element2 -> (element,element2)) read_occurences) write_occurences) in
    List.fold_left (fun acc (lhs, rhs) -> acc ||  (lhs != rhs)) false cartesian;;

let wrap_params params body =
  let params = List.mapi (fun index param -> (param,index)) params in
  let params = List.filter (fun (param, index) -> box_params param body) params in
  let params = List.map (fun (param, index) -> VarParam(param,index)) params in
  params;;

let check_var_in_list expr params= 
  let (which_list,var) = (match expr with
  | Var' (VarFree _ ) -> ([],"")
  | Var' (VarParam (varName, minor))-> (List.hd params, varName)
  | Var' (VarBound(varName, major, minor))-> (List.nth params (1 + major), varName)
  | _ -> raise X_syntax_error) in
  List.fold_left (fun acc el ->
      match el with
      | (VarParam (varName, minor)) -> acc || varName = var 
      | _ -> raise X_syntax_error
    ) false which_list;;


let rec boxing expr wrapping_params =
  match expr with
  | Const' _ -> expr
  | Set' (Var' varName, value) -> if ((check_var_in_list (Var' varName) wrapping_params) = true) then
      BoxSet' (varName, boxing value wrapping_params) else
      Set' (Var' varName, boxing value wrapping_params)
  | Var' varName -> if ((check_var_in_list expr  wrapping_params) = true) then BoxGet' varName else Var' varName
  | Seq' exprs -> Seq' (List.map (fun element -> boxing element wrapping_params) exprs)
  | Or' exprs -> Or' (List.map (fun element -> boxing element wrapping_params) exprs)
  | Def' (varName, value) -> Def' (varName, boxing value wrapping_params)
  | If' (test, dit, dif) -> If' (boxing test wrapping_params, boxing dit wrapping_params, boxing dif wrapping_params)
  | LambdaSimple' (params, body) -> 
    let wrapped_params = wrap_params params body in 
    let box_body = boxing body ([wrapped_params]@wrapping_params) in
    let params_set_box_list = set_box_list wrapped_params in
    (match 
       List.length params_set_box_list with
    | 0 -> LambdaSimple' (params, box_body)
    | _ -> LambdaSimple' (params, Seq' (params_set_box_list@[box_body])))
  | LambdaOpt' (params, param, body) -> 
    let wrapped_params = wrap_params (params@[param]) body in 
    let box_body = boxing body ([wrapped_params]@wrapping_params) in
    let params_set_box_list = set_box_list wrapped_params in
    (match 
       List.length params_set_box_list with
    | 0 -> LambdaOpt' (params,param, box_body)
    | _ -> LambdaOpt' (params,param, Seq' (params_set_box_list@[box_body])))
  | Applic' (operator, operands) -> Applic' (boxing operator wrapping_params, (List.map (fun element -> boxing element wrapping_params) operands))
  | ApplicTP' (operator, operands) -> ApplicTP' (boxing operator wrapping_params, (List.map (fun element -> boxing element wrapping_params) operands))
  | _ -> raise X_this_should_not_happen


let typeOfVar var env =
  match env with
  | [] -> VarFree(var)
  | car::cdr -> 
    let rec find x lst index =
      match lst with
      | [] -> -1
      | h :: t -> if x = h then index else  find x t (index+1) in
    let isVarParamIndex = find var car 0 in
    if (isVarParamIndex != -1) then VarParam(var, isVarParamIndex) 
    else 
      let rec findDepth x lst depth = 
        match lst with
        | [] -> VarFree(x)
        | car::cdr -> 
          let isVarInList = find var car 0 in
          if (isVarInList != -1) then VarBound(x,depth,isVarInList) else
            findDepth x cdr (depth+1) in
      findDepth var cdr 0;;


let rec lexical_addresses e env = 
  match e with
  | Const sexpr -> Const' sexpr
  | Var v -> let taggedVar = typeOfVar v env in Var'(taggedVar)
  | If(test,dit, dif) -> If'(lexical_addresses test env, lexical_addresses dit env, lexical_addresses dif env)
  | Seq exprs  -> let seqListOfLexicalAddresses = lexical_addresses_list exprs env in Seq'(seqListOfLexicalAddresses)
  | Set (varName,value) -> Set'(lexical_addresses varName env, lexical_addresses value env)
  | Def (varName, value) -> Def'(lexical_addresses varName env, lexical_addresses value env)
  | Or exprs -> let orListOfLexicalAddresses = lexical_addresses_list exprs env in Or'(orListOfLexicalAddresses)
  | LambdaSimple (params, body) -> LambdaSimple'(params, lexical_addresses body (params::env))
  | LambdaOpt (params, param, body) -> LambdaOpt'(params, param, lexical_addresses body ((params@[param])::env))
  | Applic (operator ,operands) -> let operandsListOfLexicalAddresses = lexical_addresses_list operands env in Applic'(lexical_addresses operator env, operandsListOfLexicalAddresses)

and lexical_addresses_list lst env = 
  List.map (fun expr -> lexical_addresses expr env) lst

and tail_calls e in_tp = 
  match e with
  | Const' sexpr -> Const' sexpr
  | Var' v -> Var'(v)
  | If'(test,dit, dif) -> If'(test, tail_calls dit in_tp, tail_calls dif in_tp)
  | Seq' exprs  -> let checkApplyOnLastElement = applyOnLastElement exprs in_tp  in Seq'(checkApplyOnLastElement)
  | Set' (varName,value) -> Set'(varName, tail_calls value false)
  | Def' (varName, value) -> Def'(varName, tail_calls value false)
  | Or' exprs -> let checkApplyOnLastElement = applyOnLastElement exprs in_tp in Or'(checkApplyOnLastElement)
  | LambdaSimple' (params, body) -> LambdaSimple'(params, tail_calls body true)
  | LambdaOpt' (params, param, body) -> LambdaOpt'(params, param, tail_calls body true)
  | Applic' (operator ,operands) -> let checkApplyOnLastElement = applyOnLastElement operands false in (match in_tp with
      | false -> Applic'(tail_calls operator false, checkApplyOnLastElement)
      | true -> ApplicTP'(tail_calls operator false, checkApplyOnLastElement)
    )
  | _ -> raise PC.X_no_match


and applyOnLastElement lst in_tp = 
  List.mapi (fun index element->
      if(index != (List.length lst)-1) then
        tail_calls element false else
        tail_calls element in_tp) lst




let annotate_lexical_addresses e = lexical_addresses e [];;

let annotate_tail_calls e = tail_calls e false;;

let box_set e = boxing e [];;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;

end;; (* struct Semantics *)
