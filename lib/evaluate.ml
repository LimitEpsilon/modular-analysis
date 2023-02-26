open Lambda

module Evaluator = struct
  type lbl = int

  let num_of_lbls = ref 0

  type loc = int

  let num_of_strings = ref 0

  module LEnv = Map.Make (struct
    type t = loc

    let compare = compare
  end)

  type lblexp = LVar of loc | LLam of loc * lbl | LApp of lbl * lbl

  let label_table : (lbl, lblexp) Hashtbl.t = Hashtbl.create 10
  let string_table : (string, loc) Hashtbl.t = Hashtbl.create 10
  let location_table : (loc, string) Hashtbl.t = Hashtbl.create 10

  let new_lbl () =
    incr num_of_lbls;
    !num_of_lbls

  let get_loc s =
    match Hashtbl.find string_table s with
    | l -> l
    | exception Not_found ->
        incr num_of_strings;
        Hashtbl.add string_table s !num_of_strings;
        Hashtbl.add location_table !num_of_strings s;
        !num_of_strings

  let get_string l = Hashtbl.find location_table l

  let rec label (e : lexp) =
    let lbl =
      incr num_of_lbls;
      !num_of_lbls
    in
    let lblexp =
      match e with
      | Var x -> LVar (get_loc x)
      | Lam (x, e) -> LLam (get_loc x, label e)
      | App (e1, e2) -> LApp (label e1, label e2)
    in
    Hashtbl.add label_table lbl lblexp;
    lbl

  type t = A of t LEnv.t * lbl
  type free = (lexp, loc * lbl * t LEnv.t) result

  type ctx = Free of (free -> continue) | Value of (lexp -> state)
  and continue = t * ctx
  and state = Halt of lexp | Continue of continue

  let[@tail_mod_cons] rec reduce (A (env, exp), ctx) =
    match Hashtbl.find label_table exp with
    | LVar x -> (
        match LEnv.find x env with
        | exception Not_found -> (
            match ctx with
            | Free ctx -> reduce (ctx (Ok (Var (get_string x))))
            | Value ctx -> (
                match ctx (Var (get_string x)) with
                | Halt e -> e
                | Continue k -> reduce k))
        | found -> reduce (found, ctx))
    | LLam (x, e) -> (
        match ctx with
        | Free ctx -> reduce (ctx (Error (x, e, env)))
        | Value ctx ->
            let xs = get_string x in
            reduce (A (LEnv.remove x env, e), Value (fun e -> ctx (Lam (xs, e))))
        )
    | LApp (e1, e2) ->
        let ok_case =
          match ctx with
          | Free ctx -> fun e1 e2 -> Continue (ctx (Ok (App (e1, e2))))
          | Value ctx -> fun e1 e2 -> ctx (App (e1, e2))
        in
        reduce
          ( A (env, e1),
            Free
              (function
              | Error (x, e, env1) ->
                  (A (LEnv.update x (fun _ -> Some (A (env, e2))) env1, e), ctx)
              | Ok e1 -> (A (env, e2), Value (ok_case e1))) )

  let reduce_lexp e =
    let my_lbl = label e in
    let () =
      print_string
        ("Number of syntactic locations: " ^ string_of_int !num_of_lbls ^ "\n")
    in
    let exp = reduce (A (LEnv.empty, my_lbl), Value (fun e -> Halt e)) in
    let () =
      print_string
        ("Number of locations after evaluation: " ^ string_of_int !num_of_lbls
       ^ "\n")
    in
    exp
end

module Printer = struct
  open Evaluator

  let rec finite_reduce leftover_steps (A (env, exp), ctx) =
    if leftover_steps <= 0 then
      let temp_var = Var ("[" ^ string_of_int exp ^ "]") in
      match ctx with
      | Value ctx -> (
          match ctx temp_var with
          | Halt e -> Pp.Pp.pp e
          | Continue k -> finite_reduce leftover_steps k)
      | Free ctx -> finite_reduce leftover_steps (ctx (Ok temp_var))
    else
      match Hashtbl.find label_table exp with
      | LVar x -> (
          match LEnv.find x env with
          | exception Not_found -> (
              match ctx with
              | Free ctx ->
                  finite_reduce (leftover_steps - 1)
                    (ctx (Ok (Var (get_string x))))
              | Value ctx -> (
                  match ctx (Var (get_string x)) with
                  | Halt e -> Pp.Pp.pp e
                  | Continue k -> finite_reduce (leftover_steps - 1) k))
          | found -> finite_reduce (leftover_steps - 1) (found, ctx))
      | LLam (x, e) -> (
          match ctx with
          | Free ctx ->
              finite_reduce (leftover_steps - 1) (ctx (Error (x, e, env)))
          | Value ctx ->
              let xs = get_string x in
              finite_reduce (leftover_steps - 1)
                (A (LEnv.remove x env, e), Value (fun e -> ctx (Lam (xs, e)))))
      | LApp (e1, e2) ->
          let ok_case =
            match ctx with
            | Free ctx -> fun e1 e2 -> Continue (ctx (Ok (App (e1, e2))))
            | Value ctx -> fun e1 e2 -> ctx (App (e1, e2))
          in
          finite_reduce (leftover_steps - 1)
            ( A (env, e1),
              Free
                (function
                | Error (x, e, env1) ->
                    ( A (LEnv.update x (fun _ -> Some (A (env, e2))) env1, e),
                      ctx )
                | Ok e1 -> (A (env, e2), Value (ok_case e1))) )

  let finite_step steps pgm =
    let () = print_endline "=========\nInput pgm\n=========" in
    let () =
      Pp.Pp.pp pgm;
      print_newline ();
      print_newline ()
    in
    let exp = label pgm in
    let () = print_endline "===========\nPartial pgm\n===========" in
    finite_reduce steps (A (LEnv.empty, exp), Value (fun e -> Halt e));
    print_newline ()
end
