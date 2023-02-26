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

  type ctx =
    | Free of ((lexp, string * lbl * t LEnv.t) result -> lexp)
    | Value of (lexp -> lexp)

  let[@tail_mod_cons] rec reduce (A (env, exp) : t) ctx =
    match Hashtbl.find label_table exp with
    | LVar x -> (
        match LEnv.find x env with
        | exception Not_found -> (
            match ctx with
            | Free ctx -> (ctx [@tailcall false]) (Ok (Var x))
            | Value ctx -> (ctx [@tailcall false]) (Var x))
        | found -> reduce found ctx)
    | LLam (x, e) -> (
        match ctx with
        | Free ctx -> (ctx [@tailcall false]) (Error (x, e, env))
        | Value ctx ->
            reduce
              (A (LEnv.remove x env, e))
              (Value (fun e -> ctx (Lam (x, e)))))
    | LApp (e1, e2) ->
        let ok_case =
          match ctx with
          | Free ctx -> fun e1 e2 -> ctx (Ok (App (e1, e2)))
          | Value ctx -> fun e1 e2 -> ctx (App (e1, e2))
        in
        reduce
          (A (env, e1))
          (Free
             (function
             | Error (x, e, env1) ->
                 reduce
                   (A (LEnv.update x (fun _ -> Some (A (env, e2))) env1, e))
                   ctx
             | Ok e1 -> reduce (A (env, e2)) (Value (ok_case e1))))

  let reduce_lexp e =
    let my_lbl = label e in
    let () =
      print_string
        ("Number of syntactic locations: " ^ string_of_int !num_of_lbls ^ "\n")
    in
    let exp = reduce (A (LEnv.empty, my_lbl)) (Value Fun.id) in
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

  let rec finite_reduce leftover_steps (A (env, exp) : t) ctx =
    if leftover_steps <= 0 then
      match ctx with
      | Value ctx -> ctx (Var ("[" ^ string_of_int exp ^ "]"))
      | Free ctx -> ctx (Ok (Var ("[" ^ string_of_int exp ^ "]")))
    else
      match Hashtbl.find label_table exp with
      | LVar x -> (
          match LEnv.find x env with
          | exception Not_found -> (
              match ctx with
              | Free ctx -> ctx (Ok (Var x))
              | Value ctx -> ctx (Var x))
          | found -> finite_reduce (leftover_steps - 1) found ctx)
      | LLam (x, e) -> (
          match ctx with
          | Free ctx -> ctx (Error (x, e, env))
          | Value ctx ->
              finite_reduce (leftover_steps - 1)
                (A (LEnv.remove x env, e))
                (Value (fun e -> ctx (Lam (x, e)))))
      | LApp (e1, e2) ->
          let ok_case =
            match ctx with
            | Free ctx -> fun e1 e2 -> ctx (Ok (App (e1, e2)))
            | Value ctx -> fun e1 e2 -> ctx (App (e1, e2))
          in
          finite_reduce (leftover_steps - 1)
            (A (env, e1))
            (Free
               (function
               | Error (x, e, env1) ->
                   finite_reduce (leftover_steps - 1)
                     (A (LEnv.update x (fun _ -> Some (A (env, e2))) env1, e))
                     ctx
               | Ok e1 ->
                   finite_reduce (leftover_steps - 1)
                     (A (env, e2))
                     (Value (ok_case e1))))

  let finite_step steps pgm =
    let () = print_endline "=========\nInput pgm\n=========" in
    let () =
      Pp.Pp.pp pgm;
      print_newline ()
    in
    let exp = label pgm in
    let () = print_endline "===========\nPartial pgm\n===========" in
    Pp.Pp.pp (finite_reduce steps (A (LEnv.empty, exp)) (Value Fun.id));
    print_newline ()
end
