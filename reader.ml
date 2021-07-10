
#use "pc.ml";;
open PC;;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
  
type number =
  | Fraction of int * int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Fraction (n1, d1)), Number(Fraction (n2, d2)) -> n1 = n2 && d1 = d2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | _ -> false;;

module Reader: sig
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

(* Generics *)
let letters = range_ci 'a' 'z';;
let digit   = range '0' '9';;
let lparen  = char '(';;
let rparen  = char ')';;
let hash    = char '#';;

(* Char *)
let char_prefix = caten hash (char '\\')
let visible_simple_char = guard nt_any (fun ch -> ch > ' ')

let list_to_lowercase char_list = List.map lowercase_ascii char_list

let name_to_char = fun (char_list) ->
            match (list_to_lowercase char_list) with
            | ['t';'a';'b']                 -> '\t'
            | ['r';'e';'t';'u';'r';'n']     -> '\r'
            | ['s';'p';'a';'c';'e']         -> '\032'
            | ['n';'e';'w';'l';'i';'n';'e'] -> '\n'
            | ['n';'u';'l']                 -> '\000'
            | ['p';'a';'g';'e']             -> '\012'
            |   _ -> raise X_no_match;;

let named_char = disj_list [word_ci "newline"; word_ci "nul"; word_ci "page"; word_ci "return"; word_ci "space"; word_ci "tab"]
let named_char_packed = pack named_char name_to_char

let nt_char = caten char_prefix (disj named_char_packed visible_simple_char)

let char_parser s =
  let (((hash, slash),ch), rest) = (nt_char s) in
  (Char ch, rest);;


(* Symbol *)
let symbol_char_no_dot = disj_list [digit; letters; char '!'; char '$'; char '^'; char '*'; char '-'; char '_'; char '='; char '+'; char '<'; char '>'; char '?'; char '/'; char ':'];;
let dot = char '.';;
let dot_to_string = pack dot (fun (ch) -> ("."))
let symbol_char = disj dot symbol_char_no_dot;;

let at_least_two_symbol_char_packed = pack (caten symbol_char (plus symbol_char)) (fun (ch, char_list) ->
          (list_to_string ((lowercase_ascii ch)::(list_to_lowercase char_list))))
let symbol_no_dot_packed = pack symbol_char_no_dot (fun (ch) -> list_to_string ((lowercase_ascii ch)::[]))

let nt_symbol = disj at_least_two_symbol_char_packed symbol_no_dot_packed;;

let symbol_parser s =
  let (symbol,rest) = (nt_symbol s) in
  (Symbol symbol, rest);;

(* Boolean *)
let nt_boolean_true = caten hash (char_ci 't')
let nt_boolean_false = caten hash (char_ci 'f')
let nt_boolean = disj_list [nt_boolean_true; nt_boolean_false]
let boolean_parser = pack nt_boolean (fun (hash,letter) ->
      match (lowercase_ascii letter) with
      | 't' -> Bool true
      | 'f' -> Bool false
      | _ -> raise X_no_match
    );;

(* Number *)
let natural =
  let digits = plus digit in
  pack digits (fun (ds) -> (list_to_string ds));;
let sign_adder = fun (sign,num) ->
      match sign with
      | None -> num
      | Some(result) -> if result = '-' then "-"^num else num;;

let integer = pack (caten (maybe (disj (char '+') (char '-'))) natural) sign_adder;;
let integer_parse s =
  let (num, rest) = (integer s) in
  (Number (Fraction (int_of_string num, 1)), rest);;

let rec gcd a b =
  if a = 0 then b else gcd (b mod a) a ;;
let fraction = (caten (caten integer (char '/')) natural);;
let fraction_parse s =
  let (((up, frac),down), rest) = (fraction s) in
  let d = (gcd (abs (int_of_string up)) (int_of_string down)) in
  (Number (Fraction ((int_of_string up)/d, (int_of_string down)/d)), rest);;

let float = (caten (caten integer (char '.')) natural);;
let float_parse s =
  let (((left, dot),right), rest) = (float s) in
  (Number (Float (float_of_string (left^"."^right))), rest);;

let nt_number = disj_list [fraction_parse; float_parse; integer_parse];;
let number_parser = not_followed_by nt_number (disj nt_symbol dot_to_string)

(* String *)
let quotes  = char '\"'
let backslash = char '\\'
let meta_char = disj_list[char '\\'; char '\"'; char_ci 't'; char_ci 'n'; char_ci 'r' ; char_ci 'f']
let string_meta_char = caten backslash meta_char
let meta_string_to_lower = fun ch ->
                if ('A' <= ch && 'Z' >= ch) then (lowercase_ascii ch) else ch
let two_to_meta = fun (bs, ch) ->
                match (meta_string_to_lower ch) with
                | '\\' -> '\\'
                | '\"' -> '\"'
                | 't'  -> '\t'
                | 'n'  -> '\n'
                | 'r'  -> '\r'
                | 'f'  -> '\012'
                |  _   -> raise X_no_match;;
let string_meta_char_packed = pack string_meta_char two_to_meta
let string_literal_char = guard nt_any (fun ch -> ch != '\"' && ch != '\\')
let string_char = disj string_meta_char_packed string_literal_char

let nt_string = (caten (caten quotes (star string_char)) quotes);;
let string_parser s =
  let (((quote1, str),quote2), rest) = (nt_string s) in
  (String (list_to_string str), rest);;

(* Scientific notation *)
let scientific_parser =
  let float_helper = pack float (fun ((left, dot),right) -> (float_of_string (left^"."^right))) in
  let integer_helper = pack integer (fun (num) -> (float_of_string num)) in
  let left_side = disj float_helper integer_helper in
  let nt_e = (char_ci 'e') in
  let pack_fun = (fun ((num, e),exp) -> Number(Float(num*.(10.**exp)))) in
  let scientific_str = caten (caten left_side nt_e) integer_helper in
  let scientific_num = pack scientific_str pack_fun in
  scientific_num;;

(* Comments and whitespaces *)
let whitespaces = pack nt_whitespace (fun _ -> Nil);;
let line_comment_parser =
  let line_comment_start = char ';' in
  let backslash_n = pack (char '\n') (fun _ -> "") in
  let double_backslash_n = pack (word "\\n") (fun _ -> "") in
  let end_of_in = pack nt_end_of_input (fun _ -> "") in
  let line_comment_end = disj_list [double_backslash_n; backslash_n; end_of_in;] in
  let line_comment_content = diff nt_any (disj double_backslash_n backslash_n) in
  let line_comment = caten line_comment_start (caten (star line_comment_content) line_comment_end) in
  let line_comment_packed = pack line_comment (fun _ -> Nil) in
  line_comment_packed;;

let rec parser string = ignore_parser (disj_list [dotted_list_parser; list_parser; nil_parser; string_parser; char_parser; boolean_parser; scientific_parser; number_parser; sexpr_comment_parser; quoted_parser; qquoted_parser; unquoted_parser;
unquoted_sliced_parser ;symbol_parser]) string

and dotted_list_parser string =
  let pair = caten lparen (caten (plus parser) (caten (char '.') (caten parser rparen ))) in
  let pack_fun lst cdr = List.fold_right (fun sexp rest -> Pair(sexp, rest)) lst cdr in
  let packed = pack pair (fun (l,(car,(dot, (cdr, r))))-> (pack_fun car cdr)) in
  packed string

and list_parser string =
  let pair = caten lparen (caten (star parser) rparen) in
  let pack_fun lst = List.fold_right (fun sexp rest -> Pair(sexp, rest)) lst Nil in
  let packed = pack pair (fun (l,(data, r))-> pack_fun data) in
  packed string

and nil_parser string =
  let ignore_list = disj_list [whitespaces; line_comment_parser; sexpr_comment_parser;] in
  let nil = caten (caten lparen (star ignore_list)) rparen in
  let packed = pack nil (fun _ -> Nil) in
  packed string

and ignore_parser nt =
  let ignore_list = disj_list [whitespaces; line_comment_parser; sexpr_comment_parser;] in
  let ignore nt1 = make_paired (star ignore_list) (star ignore_list) nt1 in
  ignore nt

and sexpr_comment_parser string =
  let comment = (caten (word "#;") parser) in
  let packed = pack comment (fun _ -> Nil) in
  packed string

and quoted_parser string =
  let q = (char (char_of_int 39)) in
  let qouta = caten q (ignore_parser parser) in
  let packed = pack qouta (fun (ch, sexp) -> Pair(Symbol("quote"), Pair(sexp, Nil))) in
  packed string

and qquoted_parser string =
  let q = (char '`') in
  let qouta = caten q (ignore_parser parser) in
  let packed = pack qouta (fun (ch, sexp) -> Pair(Symbol("quasiquote"), Pair(sexp, Nil))) in
  packed string

and unquoted_parser string =
  let q = (char ',') in
  let qouta = caten q (ignore_parser parser) in
  let packed = pack qouta (fun (ch, sexp) -> Pair(Symbol("unquote"), Pair(sexp, Nil))) in
  packed string

and unquoted_sliced_parser string =
  let q = (word ",@") in
  let qouta = caten q (ignore_parser parser) in
  let packed = pack qouta (fun (ch, sexp) -> Pair(Symbol("unquote-splicing"), Pair(sexp, Nil))) in
  packed string;;

let read_sexprs string =
  let (parsed, rest) = star parser (string_to_list string) in
  match rest with
  | [] -> parsed
  | _ -> raise PC.X_no_match;;

  
end;; (* struct Reader *)
