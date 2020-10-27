#use "reader.ml";;
#use "pc.ml";;
open  PC;;

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;


let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                          (expr_eq th1 th2) &&
                                          (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                           (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
    (List.for_all2 String.equal vars1 vars2) &&
    (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
    (String.equal var1 var2) &&
    (List.for_all2 String.equal vars1 vars2) &&
    (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
    (expr_eq e1 e2) &&
    (List.for_all2 expr_eq args1 args2)
  | _ -> false;;


exception X_syntax_error;;


module type TAG_PARSER = sig
   val tag_parse_expression : sexpr -> expr
   val tag_parse_expressions : sexpr list -> expr list
   end;; 
   (* signature TAG_PARSER  *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)

let tag_constants sexpr = 
  match sexpr with
  | Pair(Symbol("quote"), Pair(sexpression, Nil)) -> Const(Sexpr(sexpression))
  | Number(_) ->  Const(Sexpr(sexpr))
  | Bool(_) ->  Const(Sexpr(sexpr))
  | Char(_) ->  Const(Sexpr(sexpr))
  | String(_) -> Const(Sexpr(sexpr))
  | TaggedSexpr(tagRef,Pair(Symbol "quote", Pair(value,Nil)))->Const(Sexpr(TaggedSexpr(tagRef,value)))
  | TagRef (_) -> Const(Sexpr(sexpr)) 
  | _ -> raise PC.X_no_match ;;

let is_reserved_word word =
  match word with
  | Symbol (x) ->  List.mem x reserved_word_list
  | _ -> false


let tag_varibales sexpr = 
  match sexpr with 
  (* // CHECK! *)
  | Symbol(variable) -> if (is_reserved_word sexpr) then raise X_syntax_error else Var(variable)
  | _ -> raise PC.X_no_match ;;


let rec tag_sexpr sexpr = 
  let tagged_sexpr = disj_list [tag_constants; tag_varibales; tag_if; tag_or; tag_and; tag_mit_define; tag_define; tag_set; tag_seq;tag_lambda;tag_let;tag_let_star; tag_let_rec; tag_quasi_quote; tag_cond; tag_applic;] in
  tagged_sexpr sexpr

and tag_if sexpr = 
  match sexpr with
  | Pair(Symbol "if", Pair (test, Pair (dit, Pair (dif, Nil)))) -> 
    If(tag_sexpr test, tag_sexpr dit, tag_sexpr dif)
  | Pair(Symbol "if", Pair(test, Pair(dit, Nil)))->
    If(tag_sexpr test, tag_sexpr dit, Const(Void))
  | _ -> raise PC.X_no_match

and tag_or sexpr = 
  match sexpr with
  | Pair( Symbol "or", args) ->
    let list_of_args = pairs_to_expr_list args in 
    (match List.length list_of_args with
     | 0 -> Const(Sexpr(Bool(false)))
     | 1 -> List.hd list_of_args
     | _ -> Or(list_of_args)) 
  | _ ->  raise PC.X_no_match

and tag_and sexpr = 
  match sexpr with
  | Pair( Symbol "and", args) ->
    let list_of_args = pairs_to_expr_list args in 
    (match List.length list_of_args with
     | 0 -> Const(Sexpr(Bool(true)))
     | 1 -> List.hd list_of_args
     | _ -> (match args with 
         | Pair(car,cdr) -> tag_sexpr (Pair (Symbol "if", Pair (car, Pair (Pair (Symbol "and", cdr), Pair(Bool false, Nil))))) 
         | _ -> raise PC.X_no_match))
  | _ ->  raise PC.X_no_match

and tag_lambda sexpr = 
  match sexpr with
  | Pair(Symbol "lambda", Pair(arguments, body)) ->
    let body_as_expr_list = pairs_to_expr_list body in
    let parsed_body = (match (List.length body_as_expr_list) with
        | 0 -> raise PC.X_no_match
        | 1 -> List.hd body_as_expr_list
        | _ -> Seq(body_as_expr_list)) in

    let rec dup_exist = function
      | [] -> false
      | hd::tl -> List.exists ((=) hd) tl || dup_exist tl in

    let rec is_simple_arguments list = match list with
      | Pair(car,cdr) -> is_simple_arguments cdr
      | Nil -> true
      | _ -> false in

    let arguments_to_string_list = 
      match arguments with
      | Symbol sym -> [sym]
      | _->
        let func = (function (arg) ->( match arg with 
            | Symbol sym -> sym
            | Nil -> "nil"
            | _ -> raise PC.X_no_match)) in
        List.map func (pairs_to_list arguments) in

    if(dup_exist arguments_to_string_list ) then raise X_syntax_error else

    if(is_simple_arguments arguments) then
      LambdaSimple(arguments_to_string_list,parsed_body) 
    else
      LambdaOpt(List.rev (List.tl (List.rev arguments_to_string_list)),List.nth arguments_to_string_list (List.length arguments_to_string_list - 1),parsed_body)

  | _ -> raise PC.X_no_match 

and tag_let sexpr = 
  match sexpr with
  | Pair( Symbol "let", Pair(Nil,body))-> tag_sexpr (Pair(Pair(Symbol "lambda", Pair(Nil,body)),Nil))
  | Pair( Symbol "let", Pair(args,body))->
    let parsed_args = pairs_to_list args in
    let (params, values) = List.fold_right (fun cur (params, values) -> 
        (match cur with
         | Pair (param, Pair (vals, Nil)) -> (Pair (param, params) , Pair (vals, values))
         | _ -> raise PC.X_no_match
        )
      ) parsed_args (Nil, Nil) in
    tag_sexpr (Pair(Pair(Symbol "lambda", Pair(params,body)), values))
  | _ -> raise PC.X_no_match

and tag_let_star sexpr =
  match sexpr with
  | Pair(Symbol "let*",Pair(Nil,body)) -> tag_sexpr (Pair(Symbol "let",Pair(Nil,body)))
  | Pair(Symbol "let*",Pair(Pair(arg,Nil),body)) -> tag_sexpr (Pair(Symbol "let" ,Pair(Pair(arg,Nil),body)))
  | Pair(Symbol "let*",Pair(Pair(arg,restArgs),body)) -> tag_sexpr (Pair(Symbol "let" ,Pair(Pair(arg,Nil),Pair(Pair(Symbol "let*",Pair(restArgs,body)),Nil))))
  | _ -> raise PC.X_no_match



and tag_let_rec sexpr = 
  match sexpr with
  | Pair(Symbol "letrec",Pair(Nil,body)) -> tag_sexpr (Pair(Symbol "let", Pair(Nil,body)))
  | Pair(Symbol "letrec",Pair(Pair(arg,Nil),body)) -> 
    (match arg with
     | Pair( Symbol sym, _ )->
       tag_sexpr (Pair(Symbol("let"),Pair(Pair(Pair(Symbol sym , Pair(Pair(Symbol "quote", Pair (Symbol "whatever", Nil)),Nil)),Nil),Pair (Pair (Symbol "set!", arg),body))))
     | _ -> raise PC.X_no_match)
  | Pair(Symbol "letrec", Pair(args,body)) ->
    let parsed_args = pairs_to_list args in 
    let setBody = List.map (fun (arg) -> Pair(Symbol "set!", arg)) parsed_args in
    let setBody = List.fold_right (fun curr acc -> Pair(curr,acc) ) setBody body in
    let whateverArgs = List.map (fun (arg)-> match arg with | Pair(car,_) -> Pair(car, Pair(Pair(Symbol "quote", Pair (Symbol "whatever", Nil)),Nil)) | _ -> raise PC.X_no_match) parsed_args in
    let whateverArgs = List.fold_right (fun curr acc -> Pair(curr,acc) ) whateverArgs Nil in
    tag_sexpr (Pair(Symbol("let"),Pair((whateverArgs,setBody)))) 
  (* CHECK SOGRAIM *)
  | _ -> raise PC.X_no_match

and tag_cond sexpr = 
  match sexpr with 
  | Pair(Symbol "cond",ribs)->
    let rec parse_cond_body rib = 
      (match rib with 
       | Pair (Pair (test, Pair (Symbol "=>", Pair (thenn, Nil))), Nil) ->
         Pair (Symbol "let", Pair(Pair(Pair(Symbol "value", Pair(test, Nil)), Pair(Pair(Symbol "f", Pair(Pair(Symbol "lambda", Pair(Nil, Pair(thenn, Nil))), Nil)), Nil)), Pair(Pair(Symbol "if", Pair(Symbol "value", Pair(Pair(Pair(Symbol "f", Nil), Pair(Symbol "value", Nil)), Nil))), Nil)))
       | Pair (Pair (test, Pair (Symbol "=>", Pair (thenn, Nil))), elsee) ->
         Pair (Symbol "let", Pair (Pair (Pair (Symbol "value", Pair (test, Nil)), Pair (Pair (Symbol "f", Pair (Pair (Symbol "lambda", Pair (Nil, Pair (thenn, Nil))), Nil)), Pair(Pair(Symbol "rest", Pair(Pair(Symbol "lambda", Pair(Nil, Pair(parse_cond_body elsee, Nil))), Nil)), Nil))), Pair(Pair(Symbol "if", Pair(Symbol "value", Pair(Pair(Pair(Symbol "f", Nil), Pair(Symbol "value", Nil)), Pair(Pair(Symbol "rest", Nil), Nil)))), Nil)))
       | Pair (Pair (Symbol "else", rest), _) -> Pair (Symbol "begin", rest)
       | Pair (Pair (test, sequence), Nil) ->
         Pair (Symbol "if", Pair (test, Pair (Pair (Symbol "begin", sequence), Pair (Pair (Symbol "begin", Nil), Nil))))
       | Pair (Pair (test, sequence), rest) -> 
         Pair (Symbol "if", Pair (test, Pair (Pair (Symbol "begin", sequence), Pair (parse_cond_body rest, Nil))))
       | _ -> raise PC.X_no_match
      ) in
    tag_sexpr (parse_cond_body ribs)
  | _ -> raise PC.X_no_match


and tag_applic sexpr = 
  match sexpr with
  | Pair(operator,operands) ->
    let list_of_args = pairs_to_expr_list operands in
    if (is_reserved_word operator) then raise X_syntax_error else
      Applic(tag_sexpr operator, list_of_args)
  | _ -> raise PC.X_no_match

and tag_define sexpr = 
  match sexpr with
  | Pair( Symbol "define", Pair(name, Pair(value, Nil))) ->
    let value_to_expr = List.hd (pairs_to_expr_list (Pair(value,Nil))) in
    let tagged_name = tag_sexpr name in
    (match tagged_name with 
     | Var(variable) -> Def(Var(variable),value_to_expr)
     | _ -> raise PC.X_no_match) 
  | _ -> raise PC.X_no_match

and tag_quasi_quote sexpr = 
  match sexpr with
  | Pair(Symbol("quasiquote"),Pair(sexpression, Nil)) -> 
    let rec parse_quasi_body exp = 
      (match exp with
       | Pair (Symbol "unquote", Pair(car, Nil)) -> car
       | Pair (Symbol "unquote-splicing", Pair( _, Nil)) -> raise  PC.X_no_match
       | Symbol sym ->  (Pair(Symbol "quote", Pair(exp, Nil)))
       | Nil ->  (Pair(Symbol "quote", Pair(exp,Nil)))
       | Pair(car,cdr)->
         (match (car,cdr) with 
          | Pair (Symbol "unquote-splicing", Pair (a, Nil)), _ ->  Pair (Symbol "append", Pair (a, Pair (parse_quasi_body cdr , Nil)))
          | _ , Pair (Symbol "unquote-splicing", Pair (b ,Nil)) ->  Pair (Symbol "cons", Pair(parse_quasi_body car, Pair(b, Nil)))
          | _ -> Pair (Symbol "cons", Pair (parse_quasi_body car, Pair (parse_quasi_body cdr, Nil)))
         )
       | _ -> raise PC.X_no_match) in
    tag_sexpr (parse_quasi_body sexpression)

  | _ -> raise PC.X_no_match 


and tag_mit_define sexpr =
  match sexpr with
  | Pair( Symbol "define", Pair(Pair(name,arguments),body)) ->
    tag_sexpr (Pair ( Symbol "define", Pair(name,Pair(Pair(Symbol "lambda", Pair(arguments,body)),Nil))))
  | _ -> raise PC.X_no_match

and tag_set sexpr = 
  match sexpr with
  | Pair( Symbol "set!", Pair(name, Pair(value, Nil))) ->
    let value_to_expr = List.hd (pairs_to_expr_list (Pair(value,Nil))) in
    let tagged_name = tag_sexpr name in
    (match tagged_name with 
     | Var(variable) -> Set(Var(variable),value_to_expr)
     | _ -> raise PC.X_no_match) 
  | _ -> raise PC.X_no_match

and tag_seq sexpr = 
  match sexpr with 
  | Pair( Symbol "begin", Nil) -> Const(Void)
  | Pair( Symbol "begin", sexprs) ->
    let values_to_expr_list = pairs_to_expr_list sexprs in
    (match List.length values_to_expr_list with
     | 1 -> List.hd values_to_expr_list
     | _ -> Seq(values_to_expr_list))
  | _ -> raise PC.X_no_match

and pairs_to_list  pair =
  match pair with
  | Nil -> []
  | Pair(car,Nil) -> if (car != Nil) then [car] else []
  | Pair(car, Pair(caar , caadr)) -> car::(pairs_to_list (Pair(caar , caadr)))
  | Pair (car,cdr)-> [car;cdr]
  | _ -> raise X_syntax_error 

and pairs_to_expr_list pairs = 
  let list_of_pairs = pairs_to_list pairs in
  List.map tag_sexpr list_of_pairs;;


let tag_parse_expression sexpr = tag_sexpr sexpr;;

let tag_parse_expressions sexpr = List.map tag_sexpr sexpr;;


end;; 
(* struct Tag_Parser *)
