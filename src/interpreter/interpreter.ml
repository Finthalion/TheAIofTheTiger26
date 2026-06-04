open Ast

(* utilities to convert binary operators to an actual function *)
let binop_to_fun (op : binop) : int -> int -> int =
  match op with Add -> ( + ) | Sub -> ( - ) | Mul -> ( * ) | Div -> ( / )

let relop_to_fun (op : relop) (v1 : Value.t) (v2 : Value.t) =
  let open Value in
  match (op, v1, v2) with
  | Eq, _, _ -> if v1 = v2 then 1 else 0
  | Ne, _, _ -> if v1 <> v2 then 1 else 0
  | Lt, Int r1, Int r2 -> if r1 < r2 then 1 else 0
  | Le, Int r1, Int r2 -> if r1 <= r2 then 1 else 0
  | Gt, Int r1, Int r2 -> if r1 > r2 then 1 else 0
  | Ge, Int r1, Int r2 -> if r1 >= r2 then 1 else 0
  | Lt, String r1, String r2 -> if r1 < r2 then 1 else 0
  | Le, String r1, String r2 -> if r1 <= r2 then 1 else 0
  | Gt, String r1, String r2 -> if r1 > r2 then 1 else 0
  | Ge, String r1, String r2 -> if r1 >= r2 then 1 else 0
  | _, _, _ -> failwith "invalid comparison"

(* Evaluates an expression in a given state.  Returns the result and
   possibly updated state. *)
let rec eval_expr (state : State.t) (e : expr) : Value.t * State.t =
  match e.e_payload with
  | Const i -> (Int i, state)
  | String str -> (String str, state)
  | Lval id -> (read_lvalue state id)
  | Let (chunk, exprs) -> let scope = State.enter_scope state in
                          let ans, newscope = (eval_expr (eval_chunks scope chunk) exprs) in
                            (ans, State.exit_scope newscope)
  | Assign (left, right) -> let (value, newstate) = eval_expr state right in
                              Void, (write_lvalue state left value)
  | Seq l ->
    (
      match l with
    | [] -> Void, state
    | exp::[] -> eval_expr state exp
    | exp::list  ->
      let (value, newstate) = eval_expr state exp in
      let rest : expr = { e_loc = e.e_loc; e_payload = Seq list} in
          eval_expr newstate rest
    )
  | Binop (e1, op, e2) ->
    (
      let fn = binop_to_fun op in
      let (v1, s1) = eval_expr state e1 in
      let (v2, s2) = eval_expr s1 e2 in
      let open Value in
      (Int (fn (cast_int e1.e_loc v1) (cast_int e2.e_loc v2)), s2)
    )
  | Relop (e1, op, e2) ->
    (
      let fn = relop_to_fun op in
      let (v1, s1) = eval_expr state e1 in
      let (v2, s2) = eval_expr s1 e2 in
      (Int (fn v1 v2), s2)
    )
  | IfThenElse (clause, thenexp, None) ->
    (
      let (clauseV, s1) = eval_expr state clause in
      match clauseV with
      | Int 0 -> (Void, s1)
      | _ -> (eval_expr s1 thenexp)
    )
  | IfThenElse (clause, thenexp, Some elseexp) ->
    (
     let (clauseV, s1) = eval_expr state clause in
     match clauseV with
     | Int 0 -> (eval_expr s1 elseexp)
     | _ -> (eval_expr s1 thenexp)
    )
  | While (clause, body) ->
    (
      let (clauseV, s1) = eval_expr state clause in
      match clauseV with
      | Int 0 -> (Void, s1)
      | _ -> (
        let (_, s2) = eval_expr s1 body in
        eval_expr s2 e
      )
    )
  | ArrayInit (_, size, init) ->
      let sizeVal, state = eval_expr state size in
      let initVal, state = eval_expr state init in
      let arr = Value.array_make (Value.cast_int size.e_loc sizeVal) initVal in
      (arr, state)
  | Boolop (left, And, right) ->
    let leftVal, state = eval_expr state left in
    (match leftVal with
    | Int 0 -> (Int 0, state)
    | _ -> let rightVal, state = eval_expr state right in
      (match rightVal with
      | Int 0 -> (Int 0, state)
      | _ -> (Int 1, state)
      )
    )
  | Boolop (left, Or, right) ->
    let leftVal, state = eval_expr state left in
    (match leftVal with
    | Int 1 -> (Int 1, state)
    | _ -> let rightVal, state = eval_expr state right in
      (match rightVal with
      | Int 0 -> (Int 0, state)
      | _ -> (Int 1, state)
      )
    )
  (* evaluation from left to right *)
  | Funcall (name, args) ->
      let state, args =
        List.fold_left
          (fun (s, acc) a ->
            let r, s' = eval_expr s a in
            (s', acc @ [ r ]))
          (state, []) args
      in
      let func = State.find_fun name state in
      (func args, state)
     (* complete the function and keep this wildcard card until it becomes redundant *)

(* Writes a value to the location referred to by the given lvalue,
   returning the updated state.  This may involve evaluating
   subexpressions with side effects (e.g. array indices), and in the
   case of nested lvalues (such as array elements), recursively
   updates the structure.

   hint: Use read_lvalue, Value.array_set
 *)
and write_lvalue (state : State.t) (lv : lvalue) (value : Value.t) : State.t =
  match lv.l_payload with
  | Var id -> State.update_value id value state
  | Array (lval, index) ->
    let arr, state = read_lvalue state lval in
    let indexVal, state = eval_expr state index in
    let _ = Value.array_set (Value.cast_array lval.l_loc arr) (Value.cast_int index.e_loc indexVal) value in
    state
  (* complete the function and keep this wildcard card until it becomes redundant *)

(* Resolves an lvalue to the value it refers to, returning the value
   and the updated state.  This may involve evaluating subexpressions
   with side effects, such as index expressions.
   hint: Use Value.array_get
 *)
and read_lvalue (state : State.t) (lv : lvalue) : Value.t * State.t =
  match lv.l_payload with
  | Var id -> (State.find_value id state, state)
  | Array (lval, index) ->
    let indexVal, state = eval_expr state index in
    let arr, state = read_lvalue state lval in
    let subscript = Value.array_get (Value.cast_array lval.l_loc arr) (Value.cast_int index.e_loc indexVal) in
    (subscript, state)
    (* complete the function and keep this wildcard card until it becomes redundant *)


and eval_chunks (state : State.t) (chunks : chunk list) : State.t =
  List.fold_left eval_chunk state chunks

and eval_chunk (state : State.t) (c : chunk) : State.t =
  match c.c_payload with
  | Exp e ->
      (* we evaluate the expression so that it's side effects are taken
         into account, but the result is dicarded *)
      let _, state = eval_expr state e in
      state
  (* complete the function and keep this wildcard card until it becomes redundant *)
  | Vardec (id, _, expr) ->
    let (value, newstate) = eval_expr state expr in
      State.add_value id value newstate 
  | Typedec (_, _) -> state

open Value

let print_int out = function
  | [ Int x ] ->
      Format.fprintf out "%i%!" x;
      Void
  | [ arg ] ->
      failwith
        (Format.asprintf "type error in %s: was expecting an int but got %a"
           __FUNCTION__ Value.print arg)
  | args ->
      failwith
        (Format.asprintf
           "arity error in %s: was expecting one argument but got %i"
           __FUNCTION__ (List.length args))

let print out = function
  | [ String x ] ->
      Format.fprintf out "%s%!" x;
      Void
  | [ arg ] ->
      failwith
        (Format.asprintf "type error in %s: was expecting a string but got %a"
           __FUNCTION__ Value.print arg)
  | args ->
      failwith
        (Format.asprintf
           "arity error in %s: was expecting one argument but got %i"
           __FUNCTION__ (List.length args))

let concat = function
     (* complete the function *)
     | (String s1)::(String s2)::[] -> String (s1 ^ s2)
     | _ -> Format.asprintf "(%s) not implemented" __FUNCTION__ |> Utils.niy

let range = function
   (* complete the function *)
   | (Int min, Int max) -> let open Driver in Random.int_in_range min max
   | _ -> Format.asprintf "(%s) not implemented" __FUNCTION__ |> Utils.niy

(* Evaluates a Tiger program with an optional output formatter.
   Initializes the runtime environment with built-in functions and
   evaluates the program from the initial state. *)
let eval_program ?oc (p : program) : State.t =
  let out = match oc with None -> Format.std_formatter | Some o -> o in
  let runtime =
    [
      ("print_int", print_int out);
      ("print", print out);
      ("concat", concat);
      ("range", range);
    ]
  in
  let start = State.init runtime in
  eval_chunks start p
