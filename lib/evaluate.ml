open Lambda

module Evaluator = struct
  module LEnv = Map.Make (struct
    type t = string

    let compare = compare
  end)

  type lbl = int

  let num_of_lbls = ref 0

  type lblexp = LVar of string | LLam of string * lbl | LApp of lbl * lbl

  let label_table : (lbl, lblexp) Hashtbl.t = Hashtbl.create 10

  let new_lbl e =
    let lbl =
      incr num_of_lbls;
      !num_of_lbls
    in
    Hashtbl.add label_table lbl e;
    lbl

  let rec label (e : lexp) =
    let lbl =
      incr num_of_lbls;
      !num_of_lbls
    in
    let lblexp =
      match e with
      | Var x -> LVar x
      | Lam (x, e) -> LLam (x, label e)
      | App (e1, e2) -> LApp (label e1, label e2)
    in
    Hashtbl.add label_table lbl lblexp;
    lbl

  type t = A of t LEnv.t * lbl

  let rec lbl_to_lexp lbl =
    match Hashtbl.find label_table lbl with
    | LVar x -> Var x
    | LLam (x, e) -> Lam (x, lbl_to_lexp e)
    | LApp (e1, e2) -> App (lbl_to_lexp e1, lbl_to_lexp e2)

  let[@tail_mod_cons] rec value (A (env, exp) : t) ctx =
    match Hashtbl.find label_table exp with
    | LVar x -> (
        match LEnv.find x env with
        | exception Not_found -> (ctx [@tailcall false]) (Var x)
        | found -> value found ctx)
    | LLam (x, e) ->
        value (A (LEnv.remove x env, e)) (fun e -> ctx (Lam (x, e)))
    | LApp (e1, e2) -> (
        match free (A (env, e1)) Fun.id with
        | Error (x, e, env1) ->
            value (A (LEnv.update x (fun _ -> Some (A (env, e2))) env1, e)) ctx
        | Ok e1 -> value (A (env, e2)) (fun e -> ctx (App (e1, e))))

  and free (A (env, exp) : t) ctx =
    match Hashtbl.find label_table exp with
    | LVar x -> (
        match LEnv.find x env with
        | exception Not_found -> ctx (Ok (Var x))
        | found -> free found ctx)
    | LLam (x, e) -> ctx (Error (x, e, env))
    | LApp (e1, e2) ->
        free
          (A (env, e1))
          (function
            | Error (x, e, env1) ->
                free
                  (A (LEnv.update x (fun _ -> Some (A (env, e2))) env1, e))
                  ctx
            | Ok e1 -> ctx (Ok (value (A (env, e2)) (fun e -> App (e1, e)))))

  let reduce_lexp e =
    let my_lbl = label e in
    let () =
      print_string
        ("Number of syntactic locations: " ^ string_of_int !num_of_lbls ^ "\n")
    in
    let exp = value (A (LEnv.empty, my_lbl)) Fun.id in
    let () =
      print_string
        ("Number of locations after evaluation: " ^ string_of_int !num_of_lbls
       ^ "\n")
    in
    exp
end

module Printer = struct
  open Evaluator

  let rec repeat times x =
    if times <= 0 then ()
    else (
      print_string x;
      repeat (times - 1) x)

  let rec print_aux (depth : int) (A (env, exp) : t) =
    repeat depth " ";
    print_int exp;
    print_string " under: {";
    LEnv.iter
      (fun x v ->
        print_newline ();
        repeat depth " ";
        print_string x;
        print_string "->";
        print_aux (depth + 1) v)
      env;
    print_string "}"

  let print exp =
    print_string "Labels:\n";
    Hashtbl.iter
      (fun i exp ->
        print_int i;
        print_string ": ";
        (match exp with
        | LVar x -> print_string x
        | LLam (x, e) ->
            print_string "\\";
            print_string x;
            print_string ".";
            print_int e
        | LApp (e1, e2) ->
            print_string "@ (";
            print_int e1;
            print_string ", ";
            print_int e2;
            print_string ")");
        print_newline ())
      label_table;
    print_string "Expr:\n";
    print_aux 0 exp;
    print_newline ()

  let rec finite_value leftover_step (A (env, exp)) ctx =
    if leftover_step <= 0 then Pp.Pp.pp (ctx (Var "[]"))
    else
      match Hashtbl.find label_table exp with
      | LVar x -> (
          match LEnv.find x env with
          | exception Not_found -> Pp.Pp.pp (ctx (Var x))
          | found -> finite_value (leftover_step - 1) found ctx)
      | LLam (x, e) ->
          finite_value (leftover_step - 1)
            (A (LEnv.remove x env, e))
            (fun e -> ctx (Lam (x, e)))
      | LApp (e1, e2) -> (
          match free (A (env, e1)) Fun.id with
          | Error (x, e, env1) ->
              finite_value (leftover_step - 1)
                (A (LEnv.update x (fun _ -> Some (A (env, e2))) env1, e))
                ctx
          | Ok e1 ->
              finite_value (leftover_step - 1)
                (A (env, e2))
                (fun e -> ctx (App (e1, e))))

  let finite_step steps pgm =
    let () = print_endline "=========\nInput pgm\n=========" in
    let () =
      Pp.Pp.pp pgm;
      print_newline ()
    in
    let exp = label pgm in
    let () = print_endline "===========\nPartial pgm\n===========" in
    finite_value steps (A (LEnv.empty, exp)) Fun.id;
    print_newline ()
end
