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

  type a = A of a LEnv.t * lbl
  type free = (lexp, loc * lbl * a LEnv.t) result

  type ctx = Free of (free -> continue) | Value of (lexp -> state)
  and continue = a * ctx
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

  let rec lexp_of_lbl lbl =
    match Hashtbl.find label_table lbl with
    | LVar x -> Var (get_string x)
    | LLam (x, e) -> Lam (get_string x, lexp_of_lbl e)
    | LApp (e1, e2) -> App (lexp_of_lbl e1, lexp_of_lbl e2)

  module State = Map.Make (struct
    type t = a

    let rec compare (A (env1, exp1)) (A (env2, exp2)) =
      let first_compare = exp1 - exp2 in
      if first_compare = 0 then LEnv.compare compare env1 env2
      else first_compare
  end)

  let rec weak_reduce map =
    let for_each_relation (A (lenv, lexp)) (A (renv, rexp)) acc =
      match Hashtbl.find label_table rexp with
      | LVar x -> (
          match LEnv.find x renv with
          | exception Not_found -> acc
          | new_value -> State.add (A (lenv, lexp)) new_value acc)
      | LLam (_, _) -> acc
      | LApp (e1, e2) -> (
          (* add A (lenv, lexp) to acc *)
          match State.find (A (renv, e1)) map with
          | exception Not_found -> State.add (A (renv, e1)) (A (renv, e1)) acc
          | A (env1, exp1) -> (
              match Hashtbl.find label_table exp1 with
              | LLam (x, e) -> (
                  match State.find (A (renv, e2)) map with
                  | exception Not_found ->
                      State.add (A (renv, e2)) (A (renv, e2)) acc
                  | A (env2, exp2) -> (
                      match Hashtbl.find label_table exp2 with
                      | LLam (_, _) ->
                          let new_env =
                            LEnv.update x (fun _ -> Some (A (env2, exp2))) env1
                          in
                          State.add (A (lenv, lexp)) (A (new_env, e)) acc
                      | _ -> acc))
              | _ -> acc))
    in
    let new_map = State.fold for_each_relation map map in
    (* use physical inequality *)
    if new_map != map then weak_reduce new_map else new_map

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

  let rec lexp_of_redex (A (env, exp)) =
    match Hashtbl.find label_table exp with
    | LVar x -> (
        match LEnv.find x env with
        | exception Not_found -> Var (get_string x)
        | redex -> lexp_of_redex redex)
    | LLam (x, e) -> Lam (get_string x, lexp_of_redex (A (LEnv.remove x env, e)))
    | LApp (e1, e2) ->
        App (lexp_of_redex (A (env, e1)), lexp_of_redex (A (env, e2)))

  let weak_reduce_lexp e =
    let lbl = label e in
    let initial_exp = A (LEnv.empty, lbl) in
    let initial_state = State.add initial_exp initial_exp State.empty in
    let final_state = weak_reduce initial_state in
    let final_exp = State.find initial_exp final_state in
    lexp_of_redex final_exp
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
