open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
with show
                                                   
(* The type for the stack machine program *)
type prg = insn list

let print_prg p = List.iter (fun i -> Printf.printf "%s\n" (show(insn) i)) p
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter
     val eval : env -> config -> prg -> config
   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                                                  
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n  
                      
let rec eval env conf prog =
        match prog with
        | [] -> conf
        |inst::tail -> (
                match conf, inst with
                | (cstack, y::x::stack, tm_conf), BINOP operation -> 
                        let value = Language.Expr.binop operation(Value.to_int x) (Value.to_int y) in
                        eval env (cstack, (Value.of_int value)::stack, tm_conf) tail
                | (cstack, stack, tm_conf), CONST value ->
                        eval env (cstack, (Value.of_int value)::stack, tm_conf) tail
                | (cstack, stack, stmt_conf), STRING str -> 
                        eval env (cstack, (Value.of_string str)::stack, stmt_conf) tail
                | (cstack, stack, stmt_conf), SEXP (tag, es) ->
                        let exprs, stack' = split es stack in
                        eval env (cstack, (Value.sexp tag (List.rev exprs)) :: stack', stmt_conf) tail
				| (cstack, stack, (st, input, output)), LD x -> eval env (cstack, (State.eval st x)::stack, (st, input, output)) tail
                | (cstack, z::stack, (st, input, output)), ST x -> eval env (cstack, stack, (State.update x z st, input, output)) tail
                | (cstack, stack, (st, input, output)), STA (variable, n) -> 
                  let v::ind, stack' = split (n + 1) stack in 
                  eval env (cstack, stack', (Language.Stmt.update st variable v (List.rev ind), input, output)) tail
                | conf, LABEL label -> eval env conf tail
                | conf, JMP label -> eval env conf (env#labeled label)
                | (cstack, z::stack, tm_conf), CJMP (suf, label) -> (
                        match suf with
                        | "z" -> if Value.to_int z == 0 then eval env (cstack, stack, tm_conf) (env#labeled label)
                                 else eval env (cstack, stack, tm_conf) tail
                        | "nz" -> if Value.to_int z <> 0 then eval env (cstack, stack, tm_conf) (env#labeled label)
                                  else eval env (cstack, stack, tm_conf) tail
                        | _ -> failwith("Undefined suffix!")
                )
                | (cstack, stack, (st, input, output)), CALL (name, n, flag) -> 
                  if env#is_label name 
                  then eval env ((tail, st)::cstack, stack,(st, input, output)) (env#labeled name)
                  else eval env (env#builtin conf name n flag) tail
                | (cstack, stack, (st, input, output)), BEGIN (_, args, locals) -> 
                        let new_st = State.enter st (args @ locals) in
                        let args', rest = split (List.length args) stack in
                        let st' = List.fold_left2 (fun ast p v -> State.update p v ast) new_st args (List.rev args') in
                        eval env (cstack, rest, (st', input, output)) tail
                | (cstack, stack, (st, input, output)), END | (cstack, stack, (st, input, output)), RET _-> (
                        match cstack with
                        | (tail', st')::cstack' -> 
                               eval env (cstack', stack, (State.leave st st', input, output)) tail'
                        | [] -> conf
                )
                | (cstack, z::stack, stmt_conf), DROP -> eval env (cstack, stack, stmt_conf) tail
                | (cstack, z::stack, stmt_conf), DUP -> eval env (cstack, z::z::stack, stmt_conf) tail
                | (cstack, x::y::stack, stmt_conf), SWAP -> eval env (cstack, y::x::stack, stmt_conf) tail
                | (cstack, sexp::stack, stmt_conf), TAG s -> 
                        let res = if s = Value.tag_of sexp then 1 else 0 in
                        eval env (cstack, (Value.of_int res)::stack, stmt_conf) tail
                | (cstack, stack, (st, input, output)), ENTER es ->
                        let vals, rest = split (List.length es) stack in
                        let st' = List.fold_left2 (fun ast e var -> State.bind var e ast) State.undefined vals es in
                        eval env (cstack, rest, (State.push st st' es, input, output)) tail
                | (cstack, stack, (st, input, output)), LEAVE -> eval env (cstack, stack, (State.drop st, input, output)) tail    
        )
(* Top-level evaluation
     val run : prg -> int list -> int list
   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (* print_prg p; *)
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

(* Stack machine compiler
     val compile : Language.t -> prg
   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let compile (defs, p) = 
  let label s = "L" ^ s in
  let rec call f args p =
    let args_code = List.concat @@ List.map expr args in
    args_code @ [CALL (f, List.length args, p)]
  and pattern lfalse = function
    | Stmt.Pattern.Wildcard -> [DROP]
    | Stmt.Pattern.Ident _ -> [DROP]
    | Stmt.Pattern.Sexp (tag_name, xs) -> [DUP; TAG tag_name; CJMP ("z", lfalse)] @ List.concat (List.mapi (fun i x -> [DUP; CONST i; CALL (".elem", 2, false)] @ pattern lfalse x) xs)
    | _ -> [JMP lfalse]
  and bindings p =
    let rec inner = function
      | Stmt.Pattern.Wildcard -> [DROP]
      | Stmt.Pattern.Ident x -> [SWAP]
      | Stmt.Pattern.Sexp (_, xs) -> List.concat (List.mapi (fun i x -> [DUP; CONST i; CALL (".elem", 2, false)] @ inner x) xs) @ [DROP]
    in
    inner p @ [ENTER (Stmt.Pattern.vars p)]
  and expr e =
    match e with
      | Expr.Const c -> [CONST c]
      | Expr.Var x -> [LD x]
      | Expr.String str -> [STRING str]
      | Expr.Sexp (s, exprs) -> (List.concat (List.map expr exprs)) @ [SEXP (s, List.length exprs)]
      | Expr.Array elements -> call ".array" elements false
      | Expr.Elem (elements, i) -> call ".elem" [elements; i] false
      | Expr.Length expr -> call ".length" [expr] false
      | Expr.Binop (operation, left_op, right_op) -> expr left_op @ expr right_op @ [BINOP operation]
      | Expr.Call (name, args) -> call (label name) (List.rev args) false
  in
  let rec compile_stmt l env stmt = 
    match stmt with
    | Stmt.Assign (x,[], e) -> env, false, expr e @ [ST x]
    | Stmt.Assign (variable, indexs, e) -> 
      let code = List.concat (List.map expr (indexs @ [e])) @ [STA (variable, List.length indexs)] in 
      env, false, code
    | Stmt.Seq (frts_stmt, scnd_stmt) -> 
      let env, _, frst = compile_stmt l env frts_stmt in
      let env, _, scnd = compile_stmt l env scnd_stmt in
      env, false, frst @ scnd
    | Stmt.Skip -> env, false, []
    | Stmt.If (e, frts_stmt, scnd_stmt) ->
      let label_else, env = env#get_label in
      let label_fi, env = env#get_label in
      let env, _, fr_compile = compile_stmt l env frts_stmt in
      let env, _, sc_compile = compile_stmt l env scnd_stmt in
      env, false, expr e @ [CJMP ("z", label_else)] @ fr_compile @ [JMP label_fi; LABEL label_else] @ sc_compile @ [LABEL label_fi]
    | Stmt.While (e, st) ->
      let label_check, env = env#get_label in
      let label_loop, env = env#get_label in
      let env, _, while_body = compile_stmt l env st in
      env, false, [JMP label_check; LABEL label_loop] @ while_body @ [LABEL label_check] @ expr e @ [CJMP ("nz", label_loop)]
    | Stmt.Repeat (e, st) ->(
      let label_loop, env = env#get_label in
      let env, _,  repeat_body = compile_stmt l env st in
      env, false, [LABEL label_loop] @ repeat_body @ expr e @ [CJMP ("z", label_loop)])
    | Stmt.Call (name, args) -> env, false, call (label name) (List.rev args) true
    | Stmt.Leave -> env, false, [LEAVE]
    | Stmt.Case (e, bs) -> (
      let lend, env = env#get_label in
      let rec traverse branches env lbl n =
          match branches with
          | [] -> env, []
          | (pat, body)::branches' -> (
            let env, _, body_compiled = compile_stmt l env body in
            let lfalse, env = if n = 0 then lend, env else env#get_label in
            let env, code = traverse branches' env (Some lfalse) (n - 1) in
            env, (match lbl with None -> [] | Some l -> [LABEL l]) @ (pattern lfalse pat) @ bindings pat @ body_compiled @ [LEAVE] @ (if n = 0 then [] else [JMP lend]) @ code )
      in
      let env, code = traverse bs env None (List.length bs - 1) in
      env, false, expr e @ code @ [LABEL lend] ) 
    | Stmt.Return e -> (
      match e with
      | None -> env, false, [RET false]
      | Some e -> env, false, expr e @ [RET true] )
  in
  let compile_def env (name, (args, locals, stmt)) =
    let lend, env = env#get_label in
    let env, flag, code = compile_stmt lend env stmt in
    env,
    [LABEL name; BEGIN (name, args, locals)] @
    code @
    (if flag then [LABEL lend] else []) @
    [END]
  in
  let env =
    object
      val ls = 0
      method get_label = (label @@ string_of_int ls), {< ls = ls + 1 >}
    end
  in
  let env, def_code =
    List.fold_left
      (fun (env, code) (name, others) -> let env, code' = compile_def env (label name, others) in env, code'::code)
      (env, [])
      defs
  in
  let lend, env = env#get_label in
  let _, flag, code = compile_stmt lend env p in
  (if flag then code @ [LABEL lend] else code) @ [END] @ (List.concat def_code)
