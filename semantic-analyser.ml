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
  | Set' of var * expr'
  | Def' of var * expr'
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
  | Box'(VarFree v1), Box'(VarFree v2) -> String.equal v1 v2
  | Box'(VarParam (v1,mn1)), Box'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Box'(VarBound (v1,mj1,mn1)), Box'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | BoxGet'(VarFree v1), BoxGet'(VarFree v2) -> String.equal v1 v2
  | BoxGet'(VarParam (v1,mn1)), BoxGet'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | BoxGet'(VarBound (v1,mj1,mn1)), BoxGet'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | BoxSet'(VarFree v1,e1), BoxSet'(VarFree v2, e2) -> String.equal v1 v2 && (expr'_eq e1 e2)
  | BoxSet'(VarParam (v1,mn1), e1), BoxSet'(VarParam (v2,mn2),e2) -> String.equal v1 v2 && mn1 = mn2 && (expr'_eq e1 e2)
  | BoxSet'(VarBound (v1,mj1,mn1),e1), BoxSet'(VarBound (v2,mj2,mn2),e2) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2 && (expr'_eq e1 e2)
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq (Var'(var1)) (Var'(var2))) &&
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

  let rec index_of var lst i =
    match lst with
    | e::es -> if e = var then i else (index_of var es i+1)
    | [] -> (-1) ;;

  let make_var_param_or_bound lst var major =
    let index = index_of var lst 0 in
    match major with
    | 0 -> VarParam(var, index)
    | _ -> VarBound(var, (major-1), index);;

  let rec make_var env var major =
  match env with
  | e::es -> if (List.mem var e) then (make_var_param_or_bound e var major) else (make_var es var (major+1))
  | [] -> VarFree(var)

  let var_v exp =
    match exp with
    | Var'(v) -> v
    | _ -> raise X_syntax_error;;

  let rec index_of var lst i =
    match lst with
    | e::es -> if e = var then i else (index_of var es i+1)
    | [] -> (-1) ;;

  let make_var_param_or_bound lst var major =
    let index = index_of var lst 0 in
    match major with
    | 0 -> VarParam(var, index)
    | _ -> VarBound(var, (major-1), index);;

  let rec make_var env var major =
  match env with
  | e::es -> if (List.mem var e) then (make_var_param_or_bound e var major) else (make_var es var (major+1))
  | [] -> VarFree(var)

  let var_v exp =
    match exp with
    | Var'(v) -> v
    | _ -> raise X_syntax_error;;

  let rec lexical_adress env exp =
    match exp with
    | Const(e) -> Const'(e)
    | Var(e) -> Var'(make_var env e 0)
    | If(test,thn,els) -> If'(lexical_adress env test, lexical_adress env thn, lexical_adress env els)
    | Seq(exp_list) -> Seq'(List.map (lexical_adress env) exp_list)
    | Set(v, e) -> Set'(var_v (lexical_adress env v), lexical_adress env e)
    | Def(v, e) -> Def'(var_v (lexical_adress env v), lexical_adress env e)
    | Or(exp_list) -> Or'(List.map (lexical_adress env) exp_list)
    | LambdaSimple(args, exp) -> make_lambda_simple args exp env
    | LambdaOpt(args, opt_arg, exp) -> make_lambda_opt args opt_arg exp env
    | Applic(op, exp_list) -> Applic'(lexical_adress env op, List.map (lexical_adress env) exp_list)

  and make_lambda_simple args exp env =
    let new_env = args::env in
    LambdaSimple'(args, lexical_adress new_env exp)

  and make_lambda_opt args opt_arg exp env =
    let new_args = args@[opt_arg] in
    let new_env = new_args::env in
    LambdaOpt'(args, opt_arg, lexical_adress new_env exp);;

  let annotate_lexical_addresses e = lexical_adress [] e;;

  let rec tail_call exp tp=
    match exp, tp with
    | Const'(e), _ -> Const'(e)
    | Var'(e),_ -> Var'(e)
    | If'(test,thn,els), tp -> If'(tail_call test false, tail_call thn tp, tail_call els tp)
    | Seq'(exp_list), tp -> Seq'(my_map exp_list tp)
    | Set'(v, e), _ -> Set'(v, tail_call e false)
    | Def'(v, e), _ -> Def'(v, tail_call e false)
    | Or'(exp_list), tp -> Or'(my_map exp_list tp)
    | LambdaSimple'(args, body), _ -> LambdaSimple'(args, tail_call body true)
    | LambdaOpt'(args, opt_arg, body), _ -> LambdaOpt'(args, opt_arg, tail_call body true)
    | Applic'(op, exp_list), true -> ApplicTP'(tail_call op false, List.map (fun exp -> tail_call exp false) exp_list)
    | Applic'(op, exp_list), false -> Applic'(tail_call op false, List.map (fun exp -> tail_call exp false) exp_list)
    | _, _ -> exp

  and my_map lst tp =
    match lst with
    | e::[] -> (tail_call e tp)::(my_map [] tp)
    | e::es -> (tail_call e false)::(my_map es tp)
    | [] -> [];;

  let annotate_tail_calls e = tail_call e false;;

  let rec reads_array arg c_read body =
    (* arg = Var'(v), c_read = int counter, body = expr' *)
    match body with
    | Const'(e)-> []
    | Var'(e)-> (match e with
                | VarFree(v) -> []
                | VarParam(v,minor) -> if (expr'_eq body arg) then [-1] else []
                | VarBound(v, major, minor) -> if (expr'_eq body arg) then [-1] else [])
    | If'(test,thn,els) -> (reads_array arg c_read test) @ (reads_array arg c_read thn) @ (reads_array arg c_read els)
    | Seq'(exp_list) -> List.flatten (List.map (reads_array arg c_read) exp_list) (*raise TODO*)
    | Set'(v, e) -> reads_array arg c_read e
    | Def'(v, e) -> reads_array arg c_read e
    | Or'(exp_list) -> List.flatten (List.map (reads_array arg c_read) exp_list)
    | LambdaSimple'(args, e) -> c_read := (!c_read + 1); handle_lambda_read args e arg c_read
    | LambdaOpt'(args, opt_arg, e) -> c_read := (!c_read + 1); handle_lambda_read (args@[opt_arg] ) e arg c_read
    | Applic'(op, exp_list) | ApplicTP'(op, exp_list) -> (reads_array arg c_read op)@(List.flatten (List.map (reads_array arg c_read) exp_list))
    | _-> []

  and handle_lambda_read args body param counter =
    let new_arg =
      (match param with
      | Var'(VarParam(v,minor)) -> Var'(VarBound(v, 0, minor))
      | Var'(VarBound(v, major, minor)) -> Var'(VarBound(v, (major+1), minor))
      | _ -> raise X_syntax_error ) in
    let rib_count = !counter in
    let box_read_array = reads_array new_arg counter body in
    if (box_read_array <> []) then [rib_count] else [];;

  let rec writes_array arg c_write body =
    (* arg = Var'(v), c_write = int counter, body = expr' *)
    match body with
    | Const'(e)-> []
    | Var'(e)-> []
    | If'(test,thn,els) -> (writes_array arg c_write test) @ (writes_array arg c_write thn) @ (writes_array arg c_write els)
    | Seq'(exp_list) -> List.flatten (List.map (writes_array arg c_write) exp_list) (** raise TODO *)
    | Set'(v, e) -> (match v with
                    | VarFree(x) -> []
                    | VarParam(x,minor) -> if (expr'_eq (Var'(v)) arg) then [-1] else []
                    | VarBound(x, major, minor) -> if (expr'_eq (Var'(v)) arg) then [-1] else []) @ (writes_array arg c_write e)
    | Def'(v, e) -> writes_array arg c_write e
    | Or'(exp_list) -> List.flatten (List.map (writes_array arg c_write) exp_list)
    | LambdaSimple'(args, e) -> c_write := (!c_write + 1); handle_lambda_write args e arg c_write
    | LambdaOpt'(args, opt_arg, e) -> c_write := (!c_write + 1); handle_lambda_write (args@[opt_arg] ) e arg c_write
    | Applic'(op, exp_list)| ApplicTP'(op, exp_list) -> (writes_array arg c_write op)@(List.flatten (List.map (writes_array arg c_write) exp_list))
    | _-> []

  and handle_lambda_write args body param counter =
    let new_arg =
      (match param with
      | Var'(VarParam(v,minor)) -> Var'(VarBound(v, 0, minor))
      | Var'(VarBound(v, major, minor)) -> Var'(VarBound(v, (major+1), minor))
      | _ -> raise X_syntax_error ) in
    let rib_count = !counter in
    let box_writes_array = writes_array new_arg counter body in
    if (box_writes_array <> []) then [rib_count] else [];;


  (* Cond 3 start ****************)

  let rec cond_for_seq arg body =
    match body with
    | Seq'(exp_list) -> take_care_of_seq arg exp_list
    | _ -> true

  and take_care_of_seq arg exp_list =
  (* read array = seq exp index in which read appear, = [(seq_indx, rib), (seq_indx, rib) ...]
    write array = seq exp index in which read appear = [(seq_indx, rib), (seq_indx, rib) ...]*)
    let seq_r_c = (ref 0) in
    let read_array = (List.flatten (List.map (fun exp -> seq_r_c := (!seq_r_c + 1); (reads_array_seq arg !seq_r_c (ref (-1)) exp)) exp_list)) in
    let seq_w_c = (ref 0) in
    let write_array = (List.flatten (List.map (fun exp -> seq_w_c := (!seq_w_c + 1); (write_array_seq arg !seq_w_c (ref (-1)) exp)) exp_list)) in
    let machpela_cartezit = (List.concat (List.map (fun r -> List.map (fun w -> (r,w)) write_array) read_array)) in
    (* Explanation :
    after cartesian mult we have  [((read_seq_indx, read_rib), (write_seq_indx, write_rib)) .... rest_array]
    now we filter this array such that read and write indexes are different.
    now if we have more than one different pairs -> BOX is required
    if we have only one diff pair ->  check if first of them is in rib -1, if yes, box not needed, else BOX*)
    let dif_list_check lst =
      (match lst with
      | ((read_seq_indx, read_rib), (write_seq_indx, write_rib))::[] -> (match read_rib with
                                                                        | (-1) -> if (read_seq_indx < write_seq_indx) then true else true
                                                                        | _ -> (match write_rib with
                                                                                |(-1) -> if (read_seq_indx > write_seq_indx) then true else true
                                                                                | _ -> true ))
      | [] -> true
      | e::es -> true) in
    let filtered_machpela = List.filter (fun (r,w) -> ( r <> w )) machpela_cartezit in
    let cond_3 = dif_list_check filtered_machpela in
    cond_3

  and reads_array_seq arg seq_indx rib body =
  (* arg = Var'(v), c_read = int counter, body = expr' *)
  match body with
  | Var'(e)-> (match e with
              | VarFree(v) -> []
              | VarParam(v,minor) -> if (expr'_eq body arg) then [(seq_indx,-1)] else []
              | VarBound(v, major, minor) -> if (expr'_eq body arg) then [(seq_indx,-1)] else [])
  | If'(test,thn,els) -> (reads_array_seq arg seq_indx rib test) @ (reads_array_seq arg seq_indx rib thn) @ (reads_array_seq arg seq_indx rib els)
  | Seq'(exp_list) -> List.flatten (List.map (reads_array_seq arg seq_indx rib) exp_list) (*raise TODO*)
  | Set'(v, e) -> reads_array_seq arg seq_indx rib e
  | Def'(v, e) -> reads_array_seq arg seq_indx rib e
  | Or'(exp_list) -> List.flatten (List.map (reads_array_seq arg seq_indx rib) exp_list)
  | LambdaSimple'(args, e) -> rib := (!rib + 1); handle_lambda_read_seq args e arg rib seq_indx
  | LambdaOpt'(args, opt_arg, e) -> rib := (!rib + 1); handle_lambda_read_seq (args@[opt_arg] ) e arg rib seq_indx
  | Applic'(op, exp_list) | ApplicTP'(op, exp_list) -> (reads_array_seq arg seq_indx rib op)@(List.flatten (List.map (reads_array_seq arg seq_indx rib) exp_list))
  | _-> []

  and handle_lambda_read_seq args body param counter seq_indx =
  let new_arg =
    (match param with
    | Var'(VarParam(v,minor)) -> Var'(VarBound(v, 0, minor))
    | Var'(VarBound(v, major, minor)) -> Var'(VarBound(v, (major+1), minor))
    | _ -> raise X_syntax_error ) in
  let rib_count = !counter in
  let box_read_array = reads_array_seq new_arg seq_indx counter body in
  if (box_read_array <> []) then [(seq_indx, rib_count)] else []

  and write_array_seq arg seq_indx rib body =
  (* arg = Var'(v), c_read = int counter, body = expr' *)
  match body with
  | If'(test,thn,els) -> (write_array_seq arg seq_indx rib test) @ (write_array_seq arg seq_indx rib thn) @ (write_array_seq arg seq_indx rib els)
  | Seq'(exp_list) -> List.flatten (List.map (write_array_seq arg seq_indx rib) exp_list) (*raise TODO*)
  | Set'(v, e) -> (match v with
                    | VarFree(x) -> []
                    | VarParam(x,minor) -> if (expr'_eq (Var'(v)) arg) then [(seq_indx,-1)] else []
                    | VarBound(x, major, minor) -> if (expr'_eq (Var'(v)) arg) then [(seq_indx,-1)] else []) @ (write_array_seq arg seq_indx rib e)
  | Def'(v, e) -> write_array_seq arg seq_indx rib e
  | Or'(exp_list) -> List.flatten (List.map (write_array_seq arg seq_indx rib) exp_list)
  | LambdaSimple'(args, e) -> rib := (!rib + 1); handle_lambda_write_seq args e arg rib seq_indx
  | LambdaOpt'(args, opt_arg, e) -> rib := (!rib + 1); handle_lambda_write_seq (args@[opt_arg] ) e arg rib seq_indx
  | Applic'(op, exp_list) | ApplicTP'(op, exp_list) -> (write_array_seq arg seq_indx rib op)@(List.flatten (List.map (write_array_seq arg seq_indx rib) exp_list))
  | _-> []

  and handle_lambda_write_seq args body param counter seq_indx =
  let new_arg =
    (match param with
    | Var'(VarParam(v,minor)) -> Var'(VarBound(v, 0, minor))
    | Var'(VarBound(v, major, minor)) -> Var'(VarBound(v, (major+1), minor))
    | _ -> raise X_syntax_error ) in
  let rib_count = !counter in
  let box_read_array = reads_array_seq new_arg seq_indx counter body in
  if (box_read_array <> []) then [(seq_indx, rib_count)] else [];;

  (* Cond 3 end ****************)


  let is_box_need arg arg_list body =
    let minor = index_of arg arg_list 0 in
    let new_arg = Var'(VarParam(arg,minor)) in
    let read_array = reads_array new_arg (ref (-1)) body in
    let write_array = writes_array new_arg (ref (-1)) body in
    let machpela_cartezit = (List.concat (List.map (fun r -> List.map (fun w -> (r,w)) write_array) read_array)) in
    let rec find_diff lst =
      (match lst with
      | (r,w)::es -> if ( r <> w ) then true else find_diff es
      | [] -> false) in
    let cond_1_and_2 = find_diff machpela_cartezit in
    let cond_3 = cond_for_seq new_arg body in
    if cond_1_and_2 = false then false else cond_3;;


  let flat_seq exp =
    match exp with
    | Seq'(x) -> x
    | y -> [y]

  let rec box_set_box exp var_list =
    match exp with
    | Const'(e) -> Const'(e)
    | Var'(var)-> var_to_box_get var var_list
    | If'(test,thn,els) -> If'(box_set_box test var_list, box_set_box thn var_list, box_set_box els var_list)
    | Seq'(exp_list) -> Seq'(List.flatten (List.map flat_seq (List.map (fun exp -> box_set_box exp var_list) exp_list)))
    | Set'(v, value) -> set_rec v value var_list
    | Def'(v, e) -> Def'(v, box_set_box e var_list)
    | Or'(exp_list) -> Or'(List.map (fun exp -> box_set_box exp var_list) exp_list)
    | LambdaSimple'(args, body)-> LambdaSimple'(args, (lambda_body_rec args body var_list))
    | LambdaOpt'(args, opt_args, body) -> LambdaOpt'(args, opt_args, (lambda_body_rec (args@[opt_args]) body var_list))
    | Applic'(op, exp_list) -> Applic'(box_set_box op var_list, List.map (fun exp -> box_set_box exp var_list) exp_list)
    | ApplicTP'(op, exp_list) -> ApplicTP'(box_set_box op var_list, List.map (fun exp -> box_set_box exp var_list) exp_list)
    | _ -> exp

  and var_to_box_get var var_list =
    match var with
      | VarParam(name,minor) -> if (List.mem (name,-1) var_list) then BoxGet'(var) else Var'(var)
      | VarBound(name,major,minor) -> if (List.mem (name,major) var_list) then BoxGet'(var) else Var'(var)
      |_-> Var'(var)

  (* In var_list there is (name, depth), for VarParam the depth will be -1 *)
  and lambda_body_rec args body var_list =
    let updated_var_list = List.map (fun (name, depth) -> (name, depth+1)) var_list in
    let args_that_should_be_boxed = List.filter (fun arg -> is_box_need arg args body) args in
    let boxed_args = List.map (fun arg -> arg_to_box arg args) args_that_should_be_boxed in
    let normalized_args_list = List.map (fun name -> (name, -1)) args_that_should_be_boxed in
    let new_var_list = (updated_var_list @ normalized_args_list) in
    let evaled_body = box_set_box body new_var_list in
    if (List.length boxed_args) = 0 then evaled_body else Seq'(List.flatten (List.map flat_seq (List.append boxed_args [evaled_body])))


  and arg_to_box arg args =
    let arg_pos = index_of arg args 0 in
    Set'((VarParam(arg, arg_pos)), Box'(VarParam(arg, arg_pos)))

  and set_rec var value var_list =
    let evaled_value = box_set_box value var_list in
    match var with
      | VarParam(name,minor) -> if (List.mem (name,-1) var_list) then BoxSet'(var, evaled_value) else Set'(var, evaled_value)
      | VarBound(name,major,minor) -> if (List.mem (name,major) var_list) then BoxSet'(var, evaled_value) else Set'(var, evaled_value)
      | _ -> Set'(var, evaled_value)

  and name_in_varlist name var_list =
    List.mem name (List.map (fun (name, depth) -> name) var_list)

  and var_in_varlist var var_list =
    let var_name =
      match var with
      | VarParam(name, minor) -> name
      | VarBound(name, major, minor) -> name
      | VarFree(name) -> name in
    name_in_varlist var_name var_list;;

  let box_set e = box_set_box e [];;

  let run_semantics expr =
    box_set
      (annotate_tail_calls
         (annotate_lexical_addresses expr));;

  end;; (* struct Semantics *)
