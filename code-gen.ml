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
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (constant * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second
     argument is the fvars table type, and the third is an expr' that has been annotated
     by the semantic analyser.
   *)
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct

  (* ================================ CONST TABLE ================================= *)

  let remove_duplicates lst =
    let rec acc_only_first_appearance lst new_lst=
      match lst with
        | e::es -> if (List.mem e new_lst) then acc_only_first_appearance es new_lst else acc_only_first_appearance es (new_lst@[e])
        | [] -> new_lst in
    acc_only_first_appearance lst [];;

  let rec collect_sexp asts =
    match asts with
    | Const'(e)-> [e]
    | Var'(e)-> []
    | BoxSet'(v, e) -> collect_sexp e
    | If'(test,thn,els) -> (collect_sexp test) @ (collect_sexp thn) @ (collect_sexp els)
    | Seq'(exp_list) -> List.flatten (List.map collect_sexp exp_list)
    | Set'(v, e) -> collect_sexp e
    | Def'(v, e) -> collect_sexp e
    | Or'(exp_list) -> List.flatten (List.map collect_sexp exp_list)
    | LambdaSimple'(args, e) -> collect_sexp e
    | LambdaOpt'(args, opt_arg, e) -> collect_sexp e
    | Applic'(op, exp_list) | ApplicTP'(op, exp_list) -> List.flatten (List.map collect_sexp ([op]@exp_list))
    | _ -> []

  and expand_list const_list =
    let rec expand sexp = ( match sexp with
                      | Sexpr(Symbol(str)) -> [Sexpr (String (str)); sexp]
                      | Sexpr(Pair(e,es)) -> (expand (Sexpr(e)))@(expand (Sexpr(es)))@[Sexpr(e); Sexpr(es); sexp]
                      | _ -> [sexp] ) in
    let expanded_list = List.flatten (List.map expand const_list) in
    expanded_list

  and sexps_array asts =
    let collected_list = (List.flatten (List.map collect_sexp asts)) in
    let const_list_after_set_2 = remove_duplicates ([Void; Sexpr(Nil); Sexpr (Bool (false)); Sexpr (Bool (true))]@collected_list) in
    let expanded_list = expand_list const_list_after_set_2 in
    let const_list_after_set_4 = remove_duplicates expanded_list in
    const_list_after_set_4

  and size sexp =
    (match sexp with
    | Void -> 1
    | Sexpr(Bool(x)) -> 2
    | Sexpr(Nil) -> 1
    | Sexpr(Number(Fraction(x,y))) -> 17
    | Sexpr(Number(Float(x))) -> 9
    | Sexpr(Char(x)) -> 2
    | Sexpr(String(x)) -> 9+(String.length x)
    | Sexpr(Symbol(x)) -> 9
    | Sexpr(Pair(e,es)) -> 17)

  and stage_5_first const_array =
    let f str = (String.concat "," (List.map (fun c -> string_of_int (int_of_char c)) (string_to_list str))) in
    (* f "abc" -> string = "97,98,99" *)
    let offset = ref 0 in
    let offset_old = ref 0 in
    let create_tuple sexp offset_old =
      (match sexp with
      | Void -> (sexp, (offset_old, "db T_VOID"))
      | Sexpr(Bool(false)) ->(sexp, (offset_old, "db T_BOOL, 0"))
      | Sexpr(Bool(true)) ->(sexp, (offset_old, "db T_BOOL, 1"))
      | Sexpr(Nil) -> (sexp, (offset_old, "db T_NIL"))
      | Sexpr(Number(Float(x))) -> (sexp, (offset_old, "MAKE_LITERAL_FLOAT("^(string_of_float(x))^")"))
      | Sexpr(Number(Fraction(x,y))) -> (sexp, (offset_old,"MAKE_LITERAL_RATIONAL("^(string_of_int(x))^","^(string_of_int(y))^")"))
      | Sexpr(Char(x)) ->  (sexp, (offset_old, "MAKE_LITERAL_CHAR("^(string_of_int(int_of_char x))^")"))
      | Sexpr(String(x)) -> (sexp, (offset_old, "MAKE_LITERAL_STRING "^(f x)))
      | Sexpr(Symbol(x)) -> (sexp, (offset_old, "TODO"))
      | Sexpr(Pair(e,es)) -> (sexp, (offset_old, "TODO"))) in
    let increase_offset = (fun (sexp) -> offset := (!offset+(size sexp))) in
    let create_list cons_array = List.map (fun (sexp) -> offset_old := !offset; increase_offset(sexp); create_tuple sexp !offset_old) cons_array in
    create_list const_array

  and find_offset sexp lst=
    match lst with
    | (Sexpr(e),(offset,_))::es -> if sexpr_eq e sexp then string_of_int(offset) else find_offset sexp es
    | (Void,(_,_))::es -> find_offset sexp es
    | _ -> raise X_this_should_not_happen

  and stage_5_second tuple_3_list =
    let f lst tuple =
      (match tuple with
      | (Sexpr(Symbol(str)),(offset,_)) -> (Sexpr(Symbol(str)),(offset, "MAKE_LITERAL_SYMBOL(const_tbl+"^(find_offset (String(str)) lst)^")"))
      | (Sexpr(Pair(car,cdr)),(offset,_)) -> (Sexpr(Pair(car,cdr)),(offset, "MAKE_LITERAL_PAIR(const_tbl+"^(find_offset car lst)^", const_tbl+"^(find_offset cdr lst)^")"))
      | _ -> tuple
      ) in
    List.map (f tuple_3_list) tuple_3_list;;

  (* ====================== FREE VAR TABLE ================== *)

  let known_free_vars = [
    (* Type queries  *)
    "boolean?"; "flonum?"; "rational?";
    "pair?"; "null?"; "char?"; "string?";
    "procedure?"; "symbol?";
    (* String procedures *)
    "string-length"; "string-ref"; "string-set!";
    "make-string"; "symbol->string";
    (* Type conversions *)
    "char->integer"; "integer->char"; "exact->inexact";
    (* Identity test *)
    "eq?";
    (* Arithmetic ops *)
    "+"; "*"; "/"; "="; "<";
    (* Additional rational numebr ops *)
    "numerator"; "denominator"; "gcd";
    (* List ops *)
    "car"; "cdr"; "cons"; "apply"; "set-car!"; "set-cdr!"
  ]

  let isVarFree var =
    match var with
    | VarFree(v) -> [v]
    | _ -> [];;

  let collect_varfrees asts =
    let rec collect_varfrees_rec ast =
      match ast with
      | Const'(e)-> []
      | Var'(v)-> (isVarFree v)
      | If'(test,thn,els) -> (collect_varfrees_rec test) @ (collect_varfrees_rec thn) @ (collect_varfrees_rec els)
      | Seq'(exp_list) -> List.flatten (List.map collect_varfrees_rec exp_list)
      | Set'(v, e) -> (isVarFree v) @ (collect_varfrees_rec e)
      | Def'(v, e) -> (isVarFree v) @ (collect_varfrees_rec e)
      | Or'(exp_list) -> List.flatten (List.map collect_varfrees_rec exp_list)
      | LambdaSimple'(args, e) -> collect_varfrees_rec e
      | LambdaOpt'(args, opt_arg, e) -> collect_varfrees_rec e
      | Applic'(op, exp_list) | ApplicTP'(op, exp_list) -> List.flatten (List.map collect_varfrees_rec ([op] @ exp_list))
      | _ -> [] in
    List.flatten (List.map (fun ast -> collect_varfrees_rec ast) asts);;

  let lst_to_table lst =
    let rec name_index_lst lst i =
      match lst with
      | v::rest -> [(v,i)] @ (name_index_lst rest (i+1))
      | _ -> [] in
    name_index_lst lst 0;;


  (* =================================== GENERATE ================================*)

  let counter = ref 0;;
  let inc_and_get = (fun () -> counter := (!counter +1); (string_of_int !counter));;

  let rec generate_helper consts fvars exp depth =
    match exp with
    | Const'(sexp) -> (match sexp with
                      | Void -> "\nmov rax, const_tbl\n"
                      | Sexpr(s) -> "\nmov rax, const_tbl + "^(find_offset s consts)^"\n")
    | Var'(VarFree(x)) -> let location = string_of_int (get_fvar_location x fvars) in
                                "mov rax, qword [fvar_tbl + 8*" ^ location ^ "]\n"
    | Var'(VarParam(_, minor)) -> "mov rax, qword [rbp + 8 * (4 + "^(string_of_int minor) ^")]\n"
    | Var'(VarBound(_, major, minor)) -> "mov rax, qword [rbp + 8*2]\n"^
                                         "mov rax, qword [rax + 8*"^(string_of_int major) ^"]\n"^
                                         "mov rax, qword [rax + 8*"^(string_of_int minor) ^"]\n"
    | Box'(v) -> "\n"^(generate_helper consts fvars (Var'(v)) depth)^"\n"^
                  "MALLOC r8, 8\n"^
                  "mov qword[r8], rax\n"^
                  "mov rax, r8\n"
    | BoxGet'(v) -> "\n"^(generate_helper consts fvars (Var'(v)) depth)^"\n"^
                    "mov rax, qword [rax]\n"
    | BoxSet'(v, e) -> "\n"^(generate_helper consts fvars e depth)^"\n"^
                       "push rax\n"^
                       (generate_helper consts fvars (Var'(v)) depth)^"\n"^
                       "pop qword [rax]\n"^
                       "mov rax, SOB_VOID_ADDRESS\n"
    | If'(tst, th, el) -> let lelse_num = inc_and_get() in
                          let lexit_num = inc_and_get() in
                          "\n"^(generate_helper consts fvars tst depth)^"\n"^
                          "cmp rax, SOB_FALSE_ADDRESS\n"^
                          "je Lelse"^lelse_num^"\n"^
                          (generate_helper consts fvars th depth)^"\n"^
                          "jmp Lexit"^lexit_num^"\n"^
                          "Lelse"^lelse_num^":\n"^
                          (generate_helper consts fvars el depth)^"\n"^
                          "Lexit"^lexit_num^":\n"
    | Seq'(lst) -> List.fold_left (fun acc e -> acc^(generate_helper consts fvars e depth)) "\n" lst
    | Set'(VarFree(x), e) -> let location = string_of_int (get_fvar_location x fvars) in
                              "\n" ^ (generate_helper consts fvars e depth) ^
                                "mov qword [fvar_tbl + 8*" ^ location ^ "], rax\n" ^
                                "mov rax, SOB_VOID_ADDRESS\n"
    | Set'(VarParam(_, minor), e) ->  "\n"^(generate_helper consts fvars e depth)^"\n"^
                                      "mov qword [rbp + 8 * (4 + "^(string_of_int minor)^")], rax\n"^
                                      "mov rax, SOB_VOID_ADDRESS\n"
    | Set'(VarBound(_, major, minor),e) ->  "\n"^(generate_helper consts fvars e depth)^"\n"^
                                            "mov rbx, qword [rbp + 8 * 2]\n"^
                                            "mov rbx, qword [rbx + 8 * "^(string_of_int major) ^"]\n"^
                                            "mov qword [rbx + 8 * "^(string_of_int minor)^"], rax\n"^
                                            "mov rax, SOB_VOID_ADDRESS\n"
    | Def'(VarFree(x), e) -> let location = string_of_int (get_fvar_location x fvars) in
                              (generate_helper consts fvars e depth) ^ "\n" ^
                              "mov qword [fvar_tbl + 8*" ^ location ^ "], rax\n" ^
                              "mov rax, SOB_VOID_ADDRESS\n"
    | Or'(lst) -> let lexit = "Lexit" ^ inc_and_get() in
                    "\n" ^ (or_code consts fvars depth lst lexit)
    | LambdaSimple'(args, body) -> let lambda_index = inc_and_get() in
                                    let lcode = "Lcode" ^ lambda_index in
                                    let lcont = "Lcont" ^ lambda_index in
                                    "; LambdaSimple\n" ^
                                    "\n" ^ (env_code depth lambda_index) ^
                                    lcode ^ ":\n" ^
                                    "push rbp\n" ^
                                    "mov rbp, rsp\n" ^
                                    (generate_helper consts fvars body (depth + 1)) ^ "\n" ^
                                    "leave\n" ^
                                    "ret\n" ^
                                    lcont ^ ":\n"
    | LambdaOpt'(args, opt, body) -> let lambda_index = inc_and_get() in
                                      let lcode = "Lcode" ^ lambda_index in
                                      let lcont = "Lcont" ^ lambda_index in
                                      "; LambdaOpt\n" ^
                                      "\n" ^ (env_code depth lambda_index) ^
                                      lcode ^ ":\n" ^
                                      "; Adjust the stack for the optional arguments\n" ^
                                      (fix_stack_opt depth lambda_index (args@[opt])) ^
                                      "push rbp\n" ^
                                      "mov rbp, rsp\n" ^
                                      (generate_helper consts fvars body (depth + 1)) ^ "\n" ^
                                      "leave\n" ^
                                      "ret\n" ^
                                      lcont ^ ":\n"
    | Applic'(op, lst)  -> let args = List.fold_right (fun e acc -> acc^(generate_helper consts fvars e depth)^"\n push rax \n") lst "\n" in
                           let n = string_of_int (List.length lst) in
                           let proc = (generate_helper consts fvars op depth) in
                           "; Applic\n" ^
                           args^"\n push "^n^"\n"^proc^"\n"^
                           "push qword[ rax + 1 ] ;;push env (rax is all the closure, skip tag = +1)\n"^
                           "call qword[ rax + 1 + 8 ] ;;call code (rax is all the closure, skip tag = +1, skip env = +8)\n"^
                           "add rsp, 8 ;;pop env\n"^
                           "pop rbx ;;pop arg count\n"^
                           "shl rbx, 3 ;;rbx = rbx*8\n"^
                           "add rsp, rbx ;;pop args\n"
    | ApplicTP'(op, lst) -> let args = List.fold_right (fun e acc -> acc^(generate_helper consts fvars e depth)^"\n push rax \n") lst "\n" in
                           let n = string_of_int (List.length lst) in
                           let n4 = string_of_int ((List.length lst)+4) in
                           let proc = (generate_helper consts fvars op depth) in
                           args^"\n push "^n^"\n"^proc^"\n"^
                           "push qword[ rax + 1 ] ;;push env (rax is all the closure, skip tag = +1)\n"^
                           "push qword[ rbp + 8 ] ;;old ret address)\n"^
                           "push qword[rbp]    ;;backup old rbp\n"^
                           "mov r9, qword[rbp + 8*3]  ;;get old args num\n"^
                           "add r9, 4\n"^
                           "shl r9, 3             ;;set new r9 = (x+4)*8\n"^
                           ";;fix the stack\n"^
                           "SHIFT_FRAME "^n4^"    ;;args_count + 4 = n + env + ret addrs +old rbp\n"^
                           "add rsp, r9            ;;set new stack pointer\n"^
                           "pop rbp            ;;restore old rbp\n"^
                           "jmp qword[rax + 1 + 8] ;;jmp to code (rax is all the closure, skip tag = +1, skip env = +8)\n"
    | _ -> ""

  and env_code depth lambda_index =
    let lcode = "Lcode" ^ lambda_index in
    let lcont = "Lcont" ^ lambda_index in
    if depth == 0 then "MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, " ^ lcode ^ ")\n" ^
                          "jmp " ^ lcont ^ "\n"
                  else "MALLOC rbx, " ^ (string_of_int ((depth+1)*8)) ^ " ; rbx = pointer to ExtEnv\n" ^
                        "mov qword r8, [rbp + 8*2] ; r8 is a pointer to lexical env\n" ^
                        "; rbx[i+1] <- r8[i] using r9\n" ^
                        "mov rcx, 0 ; rcx is the loop var\n" ^
                        "mov rdx, " ^ (string_of_int depth) ^ "\n" ^
                        "simple_ext_loop" ^ lambda_index ^ ":\n" ^
                        "mov r9, qword [r8 + 8*rcx]\n" ^
                        "mov qword [rbx + 8*(rcx+1)], r9\n" ^
                        "inc rcx\n" ^
                        "cmp rcx, rdx\n" ^
                        "jne simple_ext_loop" ^ lambda_index ^ "\n" ^
                        "mov r10, qword [rbp + 8 * 3] ; r10 is the number of params in previous env\n" ^
                        "mov r11, r10 ; save the amount of params\n" ^
                        "shl r10, 3 ; r10 = r10 * 8 - the real size that we should save\n" ^
                        "MALLOC rdx, r10\n" ^
                        "mov rcx, 0 ; rcx is the loop var, r11 is the limit, doing the exchange using r14\n" ^
                        "cmp r11, 0 ; there is no parameters\n" ^
                        "je simple_param_end_loop" ^ lambda_index ^ "\n" ^
                        "simple_param_loop" ^ lambda_index ^ ":\n" ^
                        "mov r14, PVAR(rcx)\n" ^
                        "mov qword [rdx + 8*(rcx)], r14\n" ^
                        "inc rcx\n" ^
                        "cmp rcx, r11\n" ^
                        "jne simple_param_loop" ^ lambda_index ^ "\n" ^
                        "simple_param_end_loop" ^ lambda_index ^ ":\n" ^
                        "mov qword [rbx], rdx ; put this env in ExtEnv[0]\n" ^
                        "MAKE_CLOSURE(rax, rbx, " ^ lcode ^ ")\n" ^
                        "jmp " ^ lcont ^ "\n"

  and fix_stack_opt depth lambda_index args =
    let new_n = List.length args in
    "mov rbx, qword [rsp + 8*2] ; rbx = actual_n\n" ^
    "cmp rbx, " ^ (string_of_int new_n) ^ "\n" ^
    "jne not_eq" ^ lambda_index ^ "\n" ^ (* have to make the last elemnt a Pair *)
    "mov r8, qword [rsp + 8*(2 + rbx)]\n" ^
    "mov r10, r8 ; r10 = address of element\n" ^
    "MAKE_PAIR (r9, r10, SOB_NIL_ADDRESS) ; r9 = Pair(r10, Nil)\n" ^
    "mov qword [rsp + 8*(2 + rbx)], r9 ; stack[n-1] = Pair(element, Nil)\n" ^
    "jmp end_of_fix" ^ lambda_index ^ "\n" ^
    "not_eq" ^ lambda_index ^ ":\n" ^
    "; rbx have the actual n\n" ^
    "cmp rbx, " ^ (string_of_int new_n) ^ "\n" ^
    "jl enlarge_stack" ^ lambda_index ^ "\n" ^
    "; new_n < old_n\n" ^
    "; create list of rest element\n" ^
    "mov rcx, rbx\n" ^
    "sub rcx, " ^ (string_of_int new_n) ^ "\n" ^
    "inc rcx ; Need to Pair the last element as well\n" ^
    "mov r9, SOB_NIL_ADDRESS\n" ^
    "pair_cons_loop" ^ lambda_index ^ ":\n" ^
    "; rcx is the loop counter\n" ^
    "; r8 = element from the end of stack to the position of the pair\n" ^
    "mov r8, qword [rsp + 8*(2 + " ^ (string_of_int new_n) ^ " + rcx - 1)]\n" ^
    "MAKE_PAIR (rdx, r8, r9) ; rdx = Pair(r8, r9)\n" ^
    "; update r9\n" ^
    "mov r9, rdx\n" ^
    "dec rcx\n" ^
    "jnz pair_cons_loop" ^ lambda_index ^ "\n" ^
    "; r9 has the list\n" ^
    "mov qword [rsp + 8 * (2 + " ^ (string_of_int new_n) ^ ")], r9\n" ^
    "; adjust the stack size from n to " ^ (string_of_int new_n) ^ "\n" ^
    "mov r8, " ^ (string_of_int new_n) ^ " ; r8 = new_n\n" ^
    "add r8, 3 ; r8 = new_stack_size\n" ^
    "; We want that rdx will point to the last element\n" ^
    "mov rdx, r8\n" ^
    "; We want that r10 will point to the last element of old stack\n" ^
    "mov r8, rbx ; r8 = old_n\n" ^
    "add r8, 3 ; r8 = old_stack_size\n" ^
    "mov r10, r8\n" ^
    "shift_stack_up" ^ lambda_index ^ ":\n" ^
    "; stack[r10-1] <- stack[rdx-1] using r11\n" ^
    "dec r10\n" ^
    "dec rdx ; it is the smaller\n" ^
    "mov r11, qword [rsp + 8*rdx]\n" ^
    "mov qword [rsp + 8*r10], r11\n" ^
    "jnz shift_stack_up" ^ lambda_index ^ "\n" ^
    "; Fix rsp to point right\n" ^
    "; r10 hold the diff between this two pointers\n" ^
    "mul_small_stack_loop" ^ lambda_index ^ ":\n" ^
    "add rsp, 8\n" ^
    "dec r10\n" ^
    "jnz mul_small_stack_loop" ^ lambda_index ^ "\n" ^
    "jmp fix_n" ^ lambda_index ^ "\n" ^
    "enlarge_stack" ^ lambda_index ^ ":\n" ^
    "; old_n < new_n\n" ^
    "; shift down the stack\n" ^
    "mov r8, " ^ (string_of_int new_n) ^ " ; r8 = new_n\n" ^
    "add r8, 3 ; r8 = new_stack_size\n" ^
    "mov rdx, r8 ; rdx = new_stack_size\n" ^
    "mov r8, rbx ; r8 = old_n\n" ^
    "add r8, 3 ; r8 = old_stack_size\n" ^
    "mov r10, r8 ; r10 = old_stack_size\n" ^
    "mov r9, 0\n" ^
    "sub rsp, 8 ; we need to take down the hole stack\n" ^
    "shift_stack_down" ^ lambda_index ^ ":\n" ^
    "; stack[r9] <- stack[r9+1] using r11\n" ^
    "mov r11, qword [rsp + 8*(r9+1)]\n" ^
    "mov qword [rsp + 8*r9], r11\n" ^
    "inc r9\n" ^
    "dec r10 ; it is the smaller\n" ^
    "jnz shift_stack_down" ^ lambda_index ^ "\n" ^
    "; rsp is already fixed\n" ^
    "; put in the cleared element NIL\n" ^
    "mov qword [rsp + 8*(rdx - 1)], SOB_NIL_ADDRESS\n" ^
    "fix_n" ^ lambda_index ^ ":\n" ^
    "mov qword [rsp + 2*8], " ^ (string_of_int new_n) ^ "\n" ^
    "end_of_fix" ^ lambda_index ^ ":\n"

  and or_code consts fvars depth lst lexit =
    let or_exp_code exp =
      (generate_helper consts fvars exp depth) ^ "\n" ^
      "cmp rax, SOB_FALSE_ADDRESS\n" ^
      "jne " ^ lexit ^ "\n" in
    match lst with
    | e::[] ->  (generate_helper consts fvars e depth) ^ "\n" ^ lexit ^ ":\n"
    | e::rest -> (or_exp_code e) ^ (or_code consts fvars depth rest lexit)
    | _ -> raise X_this_should_not_happen

  and get_fvar_location x rest_fvars =
    match rest_fvars with
    | (v,i)::rest -> if v = x then i else get_fvar_location x rest
    | [] -> raise X_this_should_not_happen;;

  (* ================================= END ===================================== *)

  let make_consts_tbl asts = stage_5_second (stage_5_first (sexps_array asts));;
  let make_fvars_tbl asts = lst_to_table (remove_duplicates (known_free_vars @ (collect_varfrees asts)));;
  let generate consts fvars e = generate_helper consts fvars e 0;;
end;;
