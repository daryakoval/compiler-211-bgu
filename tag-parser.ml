#use "reader.ml";;
#use "pc.ml";;
open PC;;
open Reader;;

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
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "pset!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)

(* lambda helpers *)
let rec string_list lst =
  match lst with
  | Pair(Symbol(e),es) -> ((e)::(string_list es))
  | Nil -> []
  | _ -> raise X_syntax_error;;

let rec string_improper_list lst =
  match lst with
  | Pair(Symbol(e),Symbol(es)) -> [e]
  | Pair(Symbol(e),es) -> ((e)::(string_improper_list es))
  | Symbol(x) -> []
  | _ -> raise X_syntax_error;;

let rec find_last_item_in_list lst =
  match lst with
  | Pair(Symbol(e),Symbol(es)) -> es
  | Pair(Symbol(e),es) -> (find_last_item_in_list es)
  | Symbol(e) -> e
  | _ -> raise X_syntax_error;;

let rec lambda_args_type args =
  match args with
  | Pair(Symbol(e),es) -> (lambda_args_type es)
  | Nil -> "simple"
  | Symbol(es) -> "opt"
  | _ -> raise X_syntax_error;;

let flat_seq exp =
  match exp with
  | Seq(x) -> x
  | y -> [y]

let make_pset_body var_list =
  let counter = ref (List.length var_list) in
  let plus_c = (fun () -> counter := (!counter - 1)) in
  let folded = List.fold_right (fun var rest -> plus_c(); Pair(Pair(Symbol "set!", Pair(var, Pair(Symbol("v%"^(string_of_int !counter)), Nil))), rest)) var_list Nil in
  folded;;
  
let make_pset_ribs exp_list =
  let counter = ref (List.length exp_list) in
  let plus_c = (fun () -> counter := (!counter - 1)) in
  let folded = List.fold_right (fun exp rest -> plus_c(); Pair(Pair(Symbol("v%"^(string_of_int !counter)), Pair(exp, Nil)), rest)) exp_list Nil in
  folded;;

let rec tag_parse sexpr =
  match sexpr with
  | Nil -> Const(Void)
  | Number(x) -> Const(Sexpr(Number(x)))
  | Bool(x) -> Const(Sexpr(Bool(x)))
  | Char(x) -> Const(Sexpr(Char(x)))
  | String(x) -> Const(Sexpr(String(x)))
  | Pair(Symbol("quote"), Pair(x, Nil)) -> Const(Sexpr(x))
  | Pair(Symbol("unquote"), Pair(x, Nil)) -> Const(Sexpr(x))
  | Symbol(var) -> if (List.mem var reserved_word_list) then raise X_syntax_error else Var(var)
  | Pair(Symbol("if"), Pair(test, Pair(dit, Pair(dif, Nil)))) -> If(tag_parse test, tag_parse dit, tag_parse dif)
  | Pair(Symbol("if"), Pair(test, Pair(dit, Nil))) -> If(tag_parse test, tag_parse dit, Const(Void))
  | Pair(Symbol "define", Pair(Pair(name, args), Pair(body, Nil))) -> tag_parse (Pair(Symbol("define"), Pair(name, Pair((Pair(Symbol("lambda"), Pair(args, Pair(body, Nil)))), Nil))))
  | Pair(Symbol("define"), Pair(name, Pair(exp, Nil))) -> Def(tag_parse name, tag_parse exp)
  | Pair(Symbol("set!"), Pair(name, Pair(exp, Nil))) -> Set(tag_parse name, tag_parse exp)
  | Pair(Symbol("or"), operands) -> make_or operands
  | Pair(Symbol("lambda"), Pair(args, body)) -> (make_lambda args body)
  | Pair(Symbol("begin"), exps) -> make_sequence exps
  | Pair(Symbol("cond"), ribs) -> make_cond ribs
  | Pair(Symbol("let"), Pair(Nil, body)) -> tag_parse (Pair(Pair(Symbol "lambda", Pair(Nil, body)), Nil))
  | Pair(Symbol("let"), Pair(Pair(rib, ribs), body)) -> make_let rib ribs body
  | Pair(Symbol("let*"), Pair(Nil, body)) -> tag_parse (Pair(Symbol("let"), Pair(Nil, body)))
  | Pair(Symbol "let*", Pair(Pair(rib, ribs), body)) -> make_let_star rib ribs body
  | Pair(Symbol("letrec"), Pair(Nil, body)) -> tag_parse (Pair(Symbol("let"), Pair(Nil, body)))
  | Pair(Symbol("letrec"), Pair(Pair(rib, ribs), body)) -> make_letrec rib ribs body
  | Pair(Symbol("and"), operands) -> make_and operands
  | Pair(Symbol("pset!"), Pair(Pair(name, Pair(exp, Nil)), Nil)) -> tag_parse (Pair(Symbol("set!"), Pair(name, Pair(exp, Nil))))
  | Pair(Symbol("pset!"), (Pair(rib, ribs))) ->  make_pset rib ribs
  | Pair(Symbol("quasiquote"), Pair(rest, Nil)) -> tag_parse (make_quasi_quote rest)
  | Pair(operator, operands) -> Applic(tag_parse operator, make_exp_list operands)


and make_pset rib ribs =
  let vars_list = make_let_args_list rib ribs in
  let exp_list = make_let_values_list rib ribs in
  let body = make_pset_body vars_list in
  let ribs = make_pset_ribs exp_list in
  tag_parse (Pair(Symbol("let"), Pair(ribs,  body)))

  and make_let_args_list rib ribs =
  let extract_arg =
    match rib with
    | Pair(arg, Pair(value, Nil)) -> arg
    | _ -> raise X_syntax_error in
  match ribs with
  | Pair(e, rest) -> (extract_arg :: (make_let_args_list e rest))
  | Nil           -> [extract_arg]
  | _             -> raise X_syntax_error

and make_let_values_list rib ribs =
  let extract_value =
    match rib with
    | Pair(arg, Pair(value, Nil)) -> value
    | _ -> raise X_syntax_error in
  match ribs with
  | Pair(e, rest) -> (extract_value :: (make_let_values_list e rest))
  | Nil           -> [extract_value]
  | _             -> raise X_syntax_error

and make_let rib ribs body =
  let pack_fun lst = List.fold_right (fun sexp rest -> Pair(sexp, rest)) lst Nil in
  let args = pack_fun (make_let_args_list rib ribs) in
  let values = pack_fun (make_let_values_list rib ribs) in
  tag_parse (Pair(Pair(Symbol "lambda", Pair(args , body)), values))

and make_let_star rib ribs body =
  match ribs with
  | Nil -> tag_parse (Pair(Symbol "let", Pair(Pair(rib , Nil), body)))
  | _   -> tag_parse (Pair(Symbol "let", Pair(Pair(rib, Nil), Pair(Pair(Symbol "let*", Pair(ribs, body)), Nil))))


and make_letrec_args_whatever_list args =
  match args with
  | Pair(Pair(arg, Pair(value, Nil)),Nil) -> Pair(Pair(arg, Pair(Pair(Symbol "quote", Pair(Symbol "whatever", Nil)), Nil)), Nil)
  | Pair(Pair(arg, Pair(value, Nil)),rest) -> Pair(Pair(arg, Pair(Pair(Symbol "quote", Pair(Symbol "whatever", Nil)), Nil)), (make_letrec_args_whatever_list rest))
  | _ -> raise X_syntax_error

and make_values_to_sets_and_body args org_body =
  match args with
  | Pair(Pair(arg, Pair(value, Nil)),Nil) -> Pair(Pair(Symbol "set!", Pair(arg, Pair(value, Nil))), org_body)
  | Pair(Pair(arg, Pair(value, Nil)),rest) -> Pair(Pair(Symbol "set!", Pair(arg, Pair(value, Nil))), (make_values_to_sets_and_body rest org_body))
  | _ -> raise X_syntax_error

and make_letrec rib ribs body =
  let args = make_letrec_args_whatever_list (Pair(rib,ribs)) in
  let sets_and_body = make_values_to_sets_and_body (Pair(rib,ribs)) body in
  tag_parse (Pair(Symbol "let", Pair(args, sets_and_body)))

and make_cond ribs =
  match ribs with
  | Pair(Pair(Symbol "else", body), rest) -> tag_parse (Pair(Symbol "begin", body))
  | Pair(Pair(q, Pair(Symbol "=>", body)), Nil) -> tag_parse (Pair (Symbol "let", Pair(Pair(Pair(Symbol "value", Pair(q, Nil)), Pair(Pair(Symbol "f", Pair(Pair(Symbol "lambda", Pair(Nil, Pair(Pair(Symbol "begin", body), Nil))), Nil)), Nil)), Pair(Pair(Symbol "if", Pair(Symbol "value", Pair(Pair(Pair(Symbol "f", Nil), Pair(Symbol "value", Nil)), Pair(Pair(Symbol "begin", Pair(Nil, Nil)), Nil)))), Nil))))
  | Pair(Pair(q, Pair(Symbol "=>", body)), rest) -> tag_parse (Pair(Symbol "let", Pair(Pair(Pair(Symbol "value", Pair(q, Nil)), Pair(Pair(Symbol "f", Pair(Pair(Symbol "lambda", Pair(Nil, Pair(Pair(Symbol "begin", body), Nil))), Nil)), Pair(Pair(Symbol "rest", Pair(Pair(Symbol "lambda", Pair(Nil, Pair(make_cond_rec rest, Nil))), Nil)), Nil))), Pair(Pair(Symbol "if", Pair(Symbol "value", Pair(Pair(Pair(Symbol "f", Nil), Pair(Symbol "value", Nil)), Pair(Pair(Symbol "rest", Nil), Nil)))), Nil))))
  | Pair(Pair(q, body), rest) -> tag_parse (Pair(Symbol "if", Pair(q, Pair(Pair(Symbol "begin", body), Pair(make_cond_rec rest, Nil)))))
  | _ -> raise X_syntax_error

and make_cond_rec ribs =
  match ribs with
  | Nil -> (Pair(Symbol "begin", Pair(Nil,Nil)))
  | Pair(Pair(Symbol "else", body), rest) -> (Pair(Symbol "begin", body))
  | Pair(Pair(q, Pair(Symbol "=>", body)), Nil) -> (Pair (Symbol "let", Pair(Pair(Pair(Symbol "value", Pair(q, Nil)), Pair(Pair(Symbol "f", Pair(Pair(Symbol "lambda", Pair(Nil, Pair(Pair(Symbol "begin", body), Nil))), Nil)), Nil)), Pair(Pair(Symbol "if", Pair(Symbol "value", Pair(Pair(Pair(Symbol "f", Nil), Pair(Symbol "value", Nil)), Pair(Pair(Symbol "begin", Pair(Nil, Nil)), Nil)))), Nil))))
  | Pair(Pair(q, Pair(Symbol "=>", body)), rest) -> (Pair(Symbol "let", Pair(Pair(Pair(Symbol "value", Pair(q, Nil)), Pair(Pair(Symbol "f", Pair(Pair(Symbol "lambda", Pair(Nil, Pair(Pair(Symbol "begin", body), Nil))), Nil)), Pair(Pair(Symbol "rest", Pair(Pair(Symbol "lambda", Pair(Nil, Pair(make_cond_rec rest, Nil))), Nil)), Nil))), Pair(Pair(Symbol "if", Pair(Symbol "value", Pair(Pair(Pair(Symbol "f", Nil), Pair(Symbol "value", Nil)), Pair(Pair(Symbol "rest", Nil), Nil)))), Nil))))
  | Pair(Pair(q, body), rest) -> (Pair(Symbol "if", Pair(q, Pair(Pair(Symbol "begin", body), Pair(make_cond_rec rest, Nil)))))
  | _ -> raise X_syntax_error

and make_sequence exps =
  match exps with
  | Nil -> Const(Void)
  | Pair(e, Nil) -> tag_parse e
  | Pair(Symbol "begin", rest) -> make_sequence rest
  | Pair(Symbol(var), rest) -> if (List.mem var reserved_word_list) then
                Seq(List.flatten [(flat_seq (tag_parse (Pair((Symbol(var)), rest))))]) else
                Seq(sequence_eval_rec (Symbol(var)) rest)
  | Pair(primitive, rest) -> Seq(sequence_eval_rec primitive rest)
  | _ -> raise X_syntax_error

and sequence_eval_rec primitive rest =
  let eval_primitive_to_list =
    match primitive with
    | Pair(e, rest) -> (List.flatten [(flat_seq (tag_parse (Pair(e,rest))))])
    | e -> [(tag_parse e)] in
  match rest with
  | Pair(e, Nil) -> (List.append eval_primitive_to_list (List.flatten [flat_seq (tag_parse e)]))
  | Pair(Symbol(var), rest) -> if (List.mem var reserved_word_list) then
                (List.append eval_primitive_to_list (List.flatten [(flat_seq (tag_parse (Pair((Symbol(var)), rest))))])) else
                (List.append eval_primitive_to_list (sequence_eval_rec (Symbol(var)) rest))
  | Pair(e, rec_rest) -> (List.append eval_primitive_to_list (sequence_eval_rec e rec_rest))
  | _ -> raise X_syntax_error


and make_exp_list list =
  match list with
  | Pair(e,es) -> ((tag_parse e)::(make_exp_list es))
  | Nil -> []
  | _ -> raise X_syntax_error

and make_exp_list_from_dotted list =
  match list with
  | Pair(e,es) -> ((tag_parse e)::(make_exp_list es))
  | e -> [(tag_parse e)]

and make_or sexp =
  match sexp with
  | Nil -> tag_parse (Bool(false))
  | Pair(one, Nil) -> tag_parse one
  | _ -> Or(make_exp_list sexp)

and make_and sexp =
  match sexp with
  | Nil -> tag_parse (Bool(true))
  | Pair(one, Nil) -> tag_parse one
  | Pair(first, rest) -> tag_parse (Pair(Symbol "if", Pair(first, Pair(Pair(Symbol("and"), rest), Pair(Bool(false), Nil)))))
  | _ -> raise X_syntax_error

and make_lambda args body =
  let args_type = (lambda_args_type args) in
  match args_type with
  | "simple" -> LambdaSimple(string_list args, make_sequence body)
  | "opt" -> LambdaOpt(string_improper_list args, find_last_item_in_list args, make_sequence body)
  | _ -> raise X_syntax_error

and make_quasi_quote rest =
  match rest with
  | Pair(Symbol("unquote"), Pair(es, Nil)) -> es
  | Pair(Symbol("unquote-splicing"), es) -> raise X_syntax_error
  | Nil -> (Pair(Symbol("quote"), Pair(Nil, Nil)))
  | Symbol(e) -> (Pair(Symbol("quote"), Pair(Symbol(e), Nil)))
  | Pair(a, b) -> quasi_pair a b
  | Number(x) -> (Number(x))
  | Bool(x) -> (Bool(x))
  | Char(x) -> (Char(x))
  | String(x) -> (String(x))

and quasi_pair a b =
  match a,b with
  | Pair(Symbol("unquote-splicing"), Pair(sexp, Nil)), _ -> append sexp (make_quasi_quote b)
  | _ , Pair(Symbol("unquote-splicing"), Pair(sexp, Nil)) -> cons (make_quasi_quote a) sexp
  | _ , _ -> cons (make_quasi_quote a) (make_quasi_quote b)

and cons a b = Pair(Symbol "cons", Pair(a, Pair(b, Nil)))

and append a b = Pair(Symbol "append", Pair(a, Pair( b, Nil)));;


let tag_parse_expressions sexpr = List.map tag_parse sexpr;;


end;; (* struct Tag_Parser *)