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
  let de_bruijn : (lbl, int) Hashtbl.t = Hashtbl.create 10

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

  let rec label (e : lexp) (local_de_bruijn : int LEnv.t) =
    let lbl = new_lbl () in
    let lblexp =
      match e with
      | Var x ->
          let x = get_loc x in
          let idx = try LEnv.find x local_de_bruijn with _ -> -1 in
          Hashtbl.add de_bruijn lbl idx;
          LVar x
      | Lam (x, e) ->
          let x = get_loc x in
          let updated_de_bruijn =
            LEnv.map (fun index -> index + 1) local_de_bruijn
          in
          let lbl = label e (LEnv.add x 0 updated_de_bruijn) in
          LLam (x, lbl)
      | App (e1, e2) ->
          let lbl1 = label e1 local_de_bruijn in
          let lbl2 = label e2 local_de_bruijn in
          LApp (lbl1, lbl2)
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
              | Error (x, e, env1) -> (A (LEnv.add x (A (env, e2)) env1, e), ctx)
              | Ok e1 -> (A (env, e2), Value (ok_case e1))) )

  let rec pop_top_k l k =
    match k with
    | 0 -> l
    | k when k > 0 -> (
        match l with
        | [] -> failwith "pop_top_k: empty list"
        | _ :: tl -> pop_top_k tl (k - 1))
    | _ -> failwith "pop_top_k: negative k"

  type time = lbl * int

  let init_time = (-1, 0)
  let invalid_time = (-1, -1)

  let print_time (t : time) =
    let l, t = t in
    print_string "(";
    print_int l;
    print_string ", ";
    print_int t;
    print_string ")"

  let tick c _ t =
    let _, t = t in
    (c, t + 1)

  let store : (time list, lbl * time list) Hashtbl.t = Hashtbl.create 10

  let rec weak_reduce (c : lbl) (p : time list) (t : time) =
    match Hashtbl.find label_table c with
    | LVar _ ->
        let addr = pop_top_k p (Hashtbl.find de_bruijn c) in
        (Hashtbl.find store addr, t)
    | LLam _ -> ((c, p), t)
    | LApp (l1, l2) -> (
        let (c1, p1), t1 = weak_reduce l1 p t in
        let (c2, p2), t2 = weak_reduce l2 p t1 in
        match Hashtbl.find label_table c1 with
        | LLam (_, l) ->
            let tick = tick c p t2 in
            Hashtbl.replace store (tick :: p1) (c2, p2);
            weak_reduce l (tick :: p1) tick
        | _ -> failwith "free variables")

  let rec recover_lexp (c : lbl) (p : time list) =
    match Hashtbl.find label_table c with
    | LVar x ->
        let index = Hashtbl.find de_bruijn c in
        let kth_time = List.nth p index in
        if kth_time = invalid_time then Var (get_string x)
        else
          let c, p = Hashtbl.find store (pop_top_k p index) in
          recover_lexp c p
    | LLam (x, l) -> Lam (get_string x, recover_lexp l (invalid_time :: p))
    | LApp (l1, l2) -> App (recover_lexp l1 p, recover_lexp l2 p)

  let reduce_lexp e =
    let my_lbl = label e LEnv.empty in
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

  let print_label_table () =
    Hashtbl.iter
      (fun l ->
        print_int l;
        print_string ": ";
        function
        | LVar x ->
            print_string (get_string x);
            print_newline ()
        | LLam (x, e) ->
            print_string ("\\" ^ get_string x ^ ".");
            print_int e;
            print_newline ()
        | LApp (e1, e2) ->
            print_int e1;
            print_string "@";
            print_int e2;
            print_newline ())
      label_table

  let print_store t =
    print_string "Number of applications: ";
    print_time t;
    print_newline ();
    let join_table : (lbl list, (lbl * time list) list) Hashtbl.t =
      Hashtbl.create 10
    in
    let update_join_table p_left (l, p_right) =
      let lbl_list, _ = List.split p_left in
      match Hashtbl.find join_table lbl_list with
      | exception Not_found -> Hashtbl.add join_table lbl_list [ (l, p_right) ]
      | original ->
          Hashtbl.replace join_table lbl_list ((l, p_right) :: original)
    in
    let print_join_table list_left =
      print_string "Joined from ";
      List.iter
        (fun l ->
          print_int l;
          print_string " ")
        list_left;
      print_newline ();
      let print_entry list_right =
        let print_list l =
          List.iter
            (fun t ->
              print_time t;
              print_string " ")
            l
        in
        List.iter
          (fun (l, p_right) ->
            print_string "->";
            print_int l;
            print_string "/";
            print_list p_right;
            print_newline ())
          list_right
      in
      print_entry
    in
    Hashtbl.iter update_join_table store;
    Hashtbl.iter print_join_table join_table

  let weak_reduce_lexp e =
    let lbl = label e LEnv.empty in
    let (c, p), t = weak_reduce lbl [] init_time in
    print_store t;
    recover_lexp c p
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
    let exp = label pgm LEnv.empty in
    let () = print_endline "===========\nPartial pgm\n===========" in
    finite_reduce steps (A (LEnv.empty, exp), Value (fun e -> Halt e));
    print_newline ()
end
