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

  module FVSet = Set.Make (struct
    type t = loc

    let compare = compare
  end)

  type lblexp = LVar of loc | LLam of loc * lbl | LApp of lbl * lbl

  let label_table : (lbl, lblexp) Hashtbl.t = Hashtbl.create 10
  let string_table : (string, loc) Hashtbl.t = Hashtbl.create 10
  let location_table : (loc, string) Hashtbl.t = Hashtbl.create 10
  let fv_table : (lbl, FVSet.t) Hashtbl.t = Hashtbl.create 10

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
    let lblexp, fvset =
      match e with
      | Var x ->
          let x = get_loc x in
          (LVar x, FVSet.singleton x)
      | Lam (x, e) ->
          let x = get_loc x in
          let lbl, fvset = label e in
          (LLam (x, lbl), FVSet.remove x fvset)
      | App (e1, e2) ->
          let lbl1, fvset1 = label e1 in
          let lbl2, fvset2 = label e2 in
          (LApp (lbl1, lbl2), FVSet.union fvset1 fvset2)
    in
    Hashtbl.add label_table lbl lblexp;
    Hashtbl.add fv_table lbl fvset;
    (lbl, fvset)

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
        let fvset1 = Hashtbl.find fv_table e1 in
        let fvset2 = Hashtbl.find fv_table e2 in
        let env1 = LEnv.filter (fun x _ -> FVSet.mem x fvset1) env in
        let env2 = LEnv.filter (fun x _ -> FVSet.mem x fvset2) env in
        reduce
          ( A (env1, e1),
            Free
              (function
              | Error (x, e, env1) ->
                  (A (LEnv.update x (fun _ -> Some (A (env2, e2))) env1, e), ctx)
              | Ok e1 -> (A (env2, e2), Value (ok_case e1))) )

  type value = FVar of loc | Closure of loc * lbl * value LEnv.t
  type frame = R of value | L of lbl * value LEnv.t

  type reduce_result =
    | Pending of (loc * value * frame list)
    | Resolved of value

  let rec weak_reduce (c : lbl) (e : value LEnv.t) (k : frame list) =
    let process_k v = function
      | [] -> Resolved v
      | hd :: tl -> (
          match hd with
          | R (FVar x) -> Pending (x, v, tl)
          | R (Closure (x, l, e)) -> weak_reduce l (LEnv.add x v e) tl
          | L (l, e) -> weak_reduce l e (R v :: tl))
    in
    match Hashtbl.find label_table c with
    | LVar x -> (
        match LEnv.find x e with
        | exception Not_found -> process_k (FVar x) k
        | v -> process_k v k)
    | LLam (x, l) -> process_k (Closure (x, l, e)) k
    | LApp (l1, l2) ->
        let fvset1 = Hashtbl.find fv_table l1 in
        let fvset2 = Hashtbl.find fv_table l2 in
        let env1 = LEnv.filter (fun x _ -> FVSet.mem x fvset1) e in
        let env2 = LEnv.filter (fun x _ -> FVSet.mem x fvset2) e in
        weak_reduce l1 env1 (L (l2, env2) :: k)

  let reduce_lexp e =
    let my_lbl, _ = label e in
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

  let rec lexp_of_result = function
    | Pending (x, v, k) ->
        List.fold_left
          (fun e -> function
            | R v -> App (lexp_of_result (Resolved v), e)
            | L (l, env) -> App (e, lexp_of_lbl l env))
          (App (Var (get_string x), lexp_of_result (Resolved v)))
          k
    | Resolved v -> (
        match v with
        | FVar x -> Var (get_string x)
        | Closure (x, l, env) ->
            Lam (get_string x, lexp_of_lbl l (LEnv.remove x env)))

  and lexp_of_lbl l env =
    match Hashtbl.find label_table l with
    | LVar x -> (
        match LEnv.find x env with
        | exception Not_found -> Var (get_string x)
        | v -> lexp_of_result (Resolved v))
    | LLam (x, l) -> Lam (get_string x, lexp_of_lbl l (LEnv.remove x env))
    | LApp (l1, l2) -> App (lexp_of_lbl l1 env, lexp_of_lbl l2 env)

  let weak_reduce_lexp e =
    let lbl, _ = label e in
    lexp_of_result (weak_reduce lbl LEnv.empty [])
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
    let exp, _ = label pgm in
    let () = print_endline "===========\nPartial pgm\n===========" in
    finite_reduce steps (A (LEnv.empty, exp), Value (fun e -> Halt e));
    print_newline ()
end
