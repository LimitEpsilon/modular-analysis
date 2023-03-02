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
    let lbl = new_lbl () in
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

  let num_of_envs = ref 0
  let env_table : (loc, (lbl * loc) LEnv.t) Hashtbl.t = Hashtbl.create 10

  let new_env_address env =
    let loc = !num_of_envs in
    incr num_of_envs;
    Hashtbl.add env_table loc env;
    loc

  let changed = ref false

  let rec lexp_of_lblexp = function
    | LVar x -> Var (get_string x)
    | LLam (x, e) ->
        let e = Hashtbl.find label_table e in
        Lam (get_string x, lexp_of_lblexp e)
    | LApp (e1, e2) ->
        let e1 = Hashtbl.find label_table e1 in
        let e2 = Hashtbl.find label_table e2 in
        App (lexp_of_lblexp e1, lexp_of_lblexp e2)

  let for_each_entry tbl (lexp, lenv) (rexp, renv) =
    match rexp with
    | LVar x -> (
        let renv = Hashtbl.find env_table renv in
        match LEnv.find x renv with
        | exception Not_found -> ()
        | exp, env ->
            changed := true;
            let new_rexp = Hashtbl.find label_table exp in
            Hashtbl.replace tbl (lexp, lenv) (new_rexp, env))
    | LLam (_, _) -> ()
    | LApp (e1, e2) -> (
        match Hashtbl.find tbl (e1, renv) with
        | exception Not_found ->
            changed := true;
            Hashtbl.add tbl (e1, renv) (Hashtbl.find label_table e1, renv)
        | exp1, env1 -> (
            match exp1 with
            | LLam (x, e) ->
                changed := true;
                let new_renv =
                  new_env_address
                    (LEnv.update x
                       (fun _ -> Some (e2, renv))
                       (Hashtbl.find env_table env1))
                in
                Hashtbl.replace tbl (lexp, lenv)
                  (Hashtbl.find label_table e, new_renv)
            | _ -> ()))

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

  let weak_reduce_lexp e =
    let lbl = label e in
    let tbl = Hashtbl.create 10 in
    let env = new_env_address LEnv.empty in
    Hashtbl.add tbl (lbl, env) (Hashtbl.find label_table lbl, env);
    changed := true;
    while !changed do
      changed := false;
      Hashtbl.iter (for_each_entry tbl) tbl
    done;
    let lblexp, _ = Hashtbl.find tbl (lbl, env) in
    lexp_of_lblexp lblexp
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
