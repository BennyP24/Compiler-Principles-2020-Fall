#use "pc.ml";;
open PC;;


exception X_not_yet_implemented;;
exception X_this_should_not_happen;;

type number =
  | Int of int
  | Float of float;;

type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | TaggedSexpr of string * sexpr
  | TagRef of string;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Int n1), Number(Int n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | TaggedSexpr(name1, expr1), TaggedSexpr(name2, expr2) -> (name1 = name2) && (sexpr_eq expr1 expr2) 
  | TagRef(name1), TagRef(name2) -> name1 = name2
  | _ -> false;;

module Reader: sig
   val read_sexpr : string -> sexpr
   val read_sexprs : string -> sexpr list
   end
   = struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
        (fun ch -> (ch = (lowercase_ascii ch)))
        s) then str
  else Printf.sprintf "|%s|" str;;

let make_paired nt_left nt_right nt =
  let nt = caten nt_left nt in
  let nt = pack nt (function (_, e) -> e) in
  let nt = caten nt nt_right in
  let nt = pack nt (function (e, _) -> e) in
  nt;;

let parse_hex = char '#';;
let parse_backslash = char '\\';;
let parse_sign = maybe (disj (char '+') (char '-'));;
let parse_semicolon = char ';';;

let parse_whitespace str = let space = nt_whitespace in pack space (fun (x)-> Nil) str;;
let parse_left_parentheses = char '(';;
let parse_right_parentheses = char ')';;

let parse_boolean_values = 
  let parse_false = char_ci 'f' in 
  let parse_true = char_ci 't' in 
  disj parse_false parse_true;;

let parse_boolean str = 
  let test_val = caten parse_hex parse_boolean_values in
  pack test_val (fun (hex,bool)-> match bool with
      | ('t' | 'T') -> Bool(true)
      | ('f' | 'F') -> Bool(false)
      | _ -> raise X_no_match) str;;

let char_prefix = word "#\\" ;;
let char_newline = word_ci "newline";;
let char_nul = word_ci "nul";;
let char_page = word_ci "page";;
let char_return = word_ci "return";;
let char_tab = word_ci "tab";;
let char_space = word_ci "space";;

let return_char_of_int char=
  let string_from_char =  String.lowercase_ascii (list_to_string char) in
  match string_from_char with 
  | "newline" -> Char.chr 10
  | "nul" -> Char.chr 0
  | "page" -> Char.chr 12
  | "return" -> Char.chr 13
  | "tab" -> Char.chr 9
  | "space" -> Char.chr 32
  | _ -> raise X_no_match;;

let named_chars str = 
  let types = disj_list [char_newline; char_nul; char_page; char_return; char_tab; char_space] in
  pack types return_char_of_int str;;

let visible_char str = 
  const (fun c -> int_of_char c > 32) str;;

let parse_char str = 
  let type_of_chars = disj_list [named_chars ;visible_char] in 
  pack (caten char_prefix type_of_chars) 
    (fun (_, char) ->
       Char(char)) str;;

let letters = range_ci 'a' 'z';;
let digits = range '0' '9';;
let punctuation = one_of "!$^:*-_=+<>/?";;
let symbol_characters = disj_list [letters; digits; punctuation];;
let not_symbol = diff nt_any symbol_characters;;

let parse_symbol str = 
  pack  (plus symbol_characters)
    (fun (symbol)->
       let insensitive_case_symbol = String.lowercase_ascii (list_to_string symbol) in
       Symbol(insensitive_case_symbol)) str;;

let parse_meta_chars = one_of "rntf\"\\";;

let string_meta_chars str = 
  pack (caten parse_backslash parse_meta_chars)
    (fun (_,meta_char)-> 
       match meta_char with 
       | 'r' -> Char.chr 13
       | 'n' -> Char.chr 10
       | 't' -> Char.chr 9
       | 'f' -> Char.chr 12
       | '\"' -> Char.chr 34
       | '\\' -> Char.chr 92
       | _ -> raise X_no_match) str;;

let string_literal_chars = const (fun c -> c != '\"' && c != '\\');;

let string_chars = disj string_meta_chars string_literal_chars;;

let parse_string str =
  let between_quotes = caten (char '\"') (caten (star string_chars) (char '\"')) in
  pack between_quotes (fun (_,(string,_))-> String(list_to_string string)) str;;

let parse_natural_plus = plus digits;;
let parse_natural_star = star digits;;

let make_int (sign, number) = 
  match sign with 
  | Some '+' | None -> Int(int_of_string  (list_to_string number))
  | Some(-) -> Int(-1 * (int_of_string (list_to_string number)));;

let parse_integer str = 
  pack (caten (parse_sign) (parse_natural_plus)) make_int str;;

let make_float_of_strings lhs dot rhs = 
  let string_lhs = list_to_string lhs in
  let string_dot = String.make 1 dot in
  let string_rhs = list_to_string rhs in
  String.concat "" [string_lhs; string_dot; string_rhs];;
(123)

let make_minus_float_of_strings float = 
  let minus_string = String.make 1 '-' in
  String.concat "" [minus_string; float];;

let parse_float str = 
  let complete_float = (caten (parse_sign) (caten (parse_natural_plus) (caten (char '.') (parse_natural_star)))) in
  pack complete_float (fun (sign,(lhs,(dot, rhs)))-> 
      let float =  make_float_of_strings lhs dot rhs in
      match sign with
      | Some '+' | None -> Float(float_of_string float)
      | Some '-' -> Float(float_of_string (make_minus_float_of_strings float))
      | _ -> raise X_no_match) str;;

let parse_scientific_number str = 
  let before_e = disj parse_float parse_integer in
  let e_and_after = caten (char_ci 'e') parse_integer in
  let full_scientific = caten (before_e) (e_and_after) in
  pack full_scientific (fun (lhsNum, (e,rhsNum)) ->
      let (float_num,float_num2) = match lhsNum, rhsNum with 
        | Int(num), Int(num2) ->  (float_of_int num), (float_of_int num2)
        | Float(num), Float(num2) -> num, num2
        | Int(num), Float(num2) -> (float_of_int num), num2
        | Float(num), Int(num2) -> num, (float_of_int num2) in
      let calculation = float_num *. (10.0 ** float_num2) in
      Float(calculation)
    ) str;;

let parse_radix=
  let make_NT_digit ch_from ch_to displacement =
    let nt = const (fun ch -> ch_from <= ch && ch <= ch_to) in
    let nt = pack nt (let delta = (Char.code ch_from) - displacement in
                      fun ch -> (Char.code ch) - delta) in
    nt in
  let nt = disj (make_NT_digit '0' '9' 0)
      (make_NT_digit 'a' 'z' 10) in
  let nt = disj nt (make_NT_digit 'A' 'Z' 10) in
  let nt = plus nt in
  let nt = (caten (nt)  (caten (maybe (char '.')) (maybe (nt)))) in
  nt;;

let rec small_number base pow list  =
  match list with
  | [] -> 0.0
  | head::tail ->  let basePow = base ** pow in 
    let sum = head *. basePow in
    sum +. (small_number (base) (pow-.1.0) (tail));;


let parse_radix_number str = 
  let radix = caten (parse_hex) (caten (parse_integer) (caten (char_ci 'r') (caten parse_sign (parse_radix)))) in
  pack radix (fun (_,(base,(_,(sign,(numBeforeDot,(_,numAfterDot)))))) -> 
      let convertBase = match base with
        | Int(x) -> float_of_int x
        | Float(x) ->  x in
      let bigNumber = List.fold_left (fun a b -> int_of_float convertBase * a + b) 0 numBeforeDot in
      let aggregated_number = match numAfterDot with
        | Some [] | None -> float_of_int bigNumber
        | Some list-> 
          let numAfterDot = List.map (float_of_int) list in
          let smallNumber = small_number (convertBase) (-1.0) (numAfterDot) in
          (float_of_int bigNumber) +. smallNumber in
      
      match sign,numAfterDot with 
      | Some '+', (Some [] | None )-> Int(int_of_float aggregated_number)
      | Some '-', (Some [] | None) -> Int(int_of_float aggregated_number)
      | Some '-', (Some l) -> Float(-1.0 *. aggregated_number)
      | Some '+', (Some l) -> Float(aggregated_number)
      | _ , (Some [] | None) -> Int(int_of_float aggregated_number)
      | _ , (Some l ) -> Float(aggregated_number)
    )  
    str;;

let parse_number str = 
  let number_types = disj_list [parse_scientific_number; parse_radix_number; parse_float; parse_integer; ] in
  let complete_number = not_followed_by number_types parse_symbol in
  pack complete_number (fun number -> Number( number)) str;;


let parse_end_of_input str = 
  match str with
  | [] -> ((Char.chr 0), [])
  | _ -> raise X_no_match;;


let parse_line_comment str =
  let all_chars = (star (const (fun ch -> ch != '\n'))) in
  let comment_and_chars = caten (parse_semicolon) (all_chars) in
  let end_line = disj (char '\n') (parse_end_of_input) in
  let comment = caten comment_and_chars end_line in
  pack comment (fun comment -> Nil) str;;

let make_quote_expr quote_type sexpr = 
  let string_quote = list_to_string quote_type in
  match string_quote with
  | ",@" -> Pair(Symbol("unquote-splicing"), Pair(sexpr, Nil))
  | "'" -> Pair( Symbol("quote"), Pair(sexpr, Nil))
  | "," -> Pair(Symbol("unquote"), Pair(sexpr, Nil))
  | "`" -> Pair(Symbol("quasiquote"), Pair(sexpr,Nil))
  | _ -> raise X_no_match

let parse_tag_ref str =
  let tag_name = make_paired (word "#{") (char '}') parse_symbol in
  let tag_ref_not_tag_sexpr = not_followed_by tag_name (char '=') in
  pack tag_ref_not_tag_sexpr (fun symbol -> match symbol with 
      | Symbol(sym) -> TagRef(sym)
      | _ -> raise X_no_match) str;;

  
let rec check_dup_tag_sexp tag sexpr = 
  match sexpr with
  | TaggedSexpr(tag_name, sexpr_type) -> if tag = tag_name then raise X_this_should_not_happen else true
  | Pair(hd,tail) -> (check_dup_tag_sexp tag  hd) && (check_dup_tag_sexp tag tail)
  | _ -> true

let rec parse_all_sexpr str =
  let sexpr_types = disj_list [parse_comments;parse_boolean; parse_number; parse_char; parse_symbol; parse_string; parse_list; parse_dotted_list; parse_quote_like; parse_tagged_sexp; parse_tag_ref; parse_list_with_comments] in
  let sexpr_without_whitespaces = make_paired (star parse_comments) (star parse_comments) sexpr_types in
  sexpr_without_whitespaces str

  and parse_list_with_comments str =
    let p = caten (char '(') (caten (star parse_comments) (char ')')) in
    pack p (fun (x) -> Nil) str 


and parse_empty_list str = 
 let parenthesis = caten (char '(') (char ')') in
 pack parenthesis (fun x -> Nil) str

and parse_list str =
  let make_list = make_paired parse_left_parentheses parse_right_parentheses (star parse_all_sexpr) in
  pack make_list (fun (sexpr_list) -> List.fold_right (fun curr acc -> Pair(curr,acc)) sexpr_list Nil) str

and parse_dotted_list str =
  let sexprs_dot_sexpr = caten (plus parse_all_sexpr) (caten (char '.') parse_all_sexpr) in 
  let list_without_parentheses = make_paired parse_left_parentheses parse_right_parentheses in
  let make_dot_list = list_without_parentheses sexprs_dot_sexpr in
  pack make_dot_list (fun (sexpr_list,(_,sexpr)) -> List.fold_right (fun curr acc -> Pair(curr,acc)) sexpr_list sexpr) str

and parse_quote_like str = 
  let quote_types = disj_list [word "'"; word ",@"; word ",";  word "`" ] in
  pack (caten quote_types parse_all_sexpr) 
    (fun (quote,sexpr)-> make_quote_expr quote sexpr) str


and parse_sexpr_comment str =
  let prefix = caten parse_hex (char ';') in
  pack (caten prefix parse_all_sexpr) (fun x-> Nil) str


and  parse_comments str = 
  let comments = disj_list [(parse_line_comment) ;(parse_sexpr_comment); parse_whitespace] in
  pack comments (fun x-> Nil) str

and parse_tagged_sexp str =
  let tag_name = make_paired (word "#{") (char '}') parse_symbol in
  let tag_sexp = caten tag_name (char '=') in
  let sexp_after_tag = caten tag_sexp parse_all_sexpr in
  pack sexp_after_tag (fun ((tag,_),sexpr)-> 
  let symbol_name = match tag with
  | Symbol(name)-> name
  | _ -> raise X_this_should_not_happen in
  let dup = check_dup_tag_sexp symbol_name sexpr in 
  if dup = true then TaggedSexpr(symbol_name,sexpr) else raise X_this_should_not_happen 
  ) str;;


let read_sexpr str = 
  let (sexpr,rest) =  (plus parse_all_sexpr (string_to_list str)) in
  if (List.length sexpr) = 1 then (List.hd sexpr) else raise X_no_match;;


let read_sexprs str = 
  let (sexpr_list,rest) =  (star parse_all_sexpr) (string_to_list str) in
  sexpr_list;;




end;;
(* struct Reader *)
