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

  let rec step ((A (env, exp) : t), (stack : t list)) : t * t list =
    match Hashtbl.find label_table exp with
    | LVar x -> (
        match LEnv.find x env with
        | exception Not_found -> (A (env, exp), stack)
        | A (env, exp) -> (step [@tailcall]) (A (env, exp), stack))
    | LLam (x, e) -> (
        match stack with
        | [] -> (A (env, exp), [])
        | hd :: tl ->
            let updated_env = LEnv.update x (fun _ -> Some hd) env in
            (step [@tailcall]) (A (updated_env, e), tl))
    | LApp (e1, e2) -> (step [@tailcall]) (A (env, e1), A (env, e2) :: stack)

  let rec reduce to_eval ctx arg_stack =
    let A (env', exp'), leftover_args = step to_eval in
    match leftover_args with
    | [] -> (
        match Hashtbl.find label_table exp' with
        | LVar x ->
            let rec loop exp = function
              | [] -> exp
              | hd :: tl -> (
                  match hd with
                  | [] -> (loop [@tailcall]) exp tl
                  | hd' :: tl' ->
                      (reduce [@tailcall]) (hd', [])
                        (fun e -> App (exp, e))
                        (tl' :: tl))
            in
            loop (ctx (Var x)) arg_stack
        | LLam (x, e) ->
            (reduce [@tailcall])
              (A (LEnv.remove x env', e), [])
              (fun e -> ctx (Lam (x, e)))
              arg_stack
        | LApp (e1, e2) ->
            let e1 = lbl_to_lexp e1 in
            (reduce [@tailcall])
              (A (env', e2), [])
              (fun e -> ctx (App (e1, e)))
              arg_stack)
    | hd :: tl ->
        let exp' = lbl_to_lexp exp' in
        (reduce [@tailcall]) (hd, [])
          (fun e -> ctx (App (exp', e)))
          (tl :: arg_stack)

  let rec value (A (env, exp) : t) : lbl =
    match Hashtbl.find label_table exp with
    | LVar x -> (
        match LEnv.find x env with
        | exception Not_found -> exp
        | found -> value found)
    | LLam (x, e) ->
        let e' = value (A (LEnv.remove x env, e)) in
        let lbl' =
          incr num_of_lbls;
          !num_of_lbls
        in
        Hashtbl.add label_table lbl' (LLam (x, e'));
        lbl'
    | LApp (e1, e2) -> (
        let (A (env', exp')) = free (A (env, e1)) in
        match Hashtbl.find label_table exp' with
        | LLam (x, e) ->
            value (A (LEnv.update x (fun _ -> Some (A (env, e2))) env', e))
        | _ ->
            let lbl' =
              incr num_of_lbls;
              !num_of_lbls
            in
            Hashtbl.add label_table lbl' (LApp (exp', value (A (env, e2))));
            lbl')

  and free (A (env, exp) : t) : t =
    match Hashtbl.find label_table exp with
    | LVar x -> (
        match LEnv.find x env with
        | exception Not_found -> A (env, exp)
        | found -> free found)
    | LLam (_, _) -> A (env, exp)
    | LApp (e1, e2) -> (
        let (A (env', exp')) = free (A (env, e1)) in
        match Hashtbl.find label_table exp' with
        | LLam (x, e) ->
            free (A (LEnv.update x (fun _ -> Some (A (env, e2))) env', e))
        | _ ->
            let lbl' =
              incr num_of_lbls;
              !num_of_lbls
            in
            Hashtbl.add label_table lbl' (LApp (exp', value (A (env, e2))));
            A (env, lbl'))

  let reduce_lexp e =
    let my_lbl = label e in
    let () =
      print_string
        ("Number of syntactic locations: " ^ string_of_int !num_of_lbls ^ "\n")
    in
    let exp = reduce (A (LEnv.empty, my_lbl), []) (fun x -> x) [] in
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

  let rec finite_step_aux leftover_step to_eval ctx arg_stack =
    if leftover_step <= 0 then
      Pp.Pp.pp
        (List.fold_left
           (fun acc arg_list ->
             List.fold_left (fun acc _ -> App (acc, Var "[]")) acc arg_list)
           (ctx (Var "[]")) arg_stack)
    else
      let A (env', exp'), leftover_args = step to_eval in
      match leftover_args with
      | [] -> (
          match Hashtbl.find label_table exp' with
          | LVar x ->
              let rec loop exp = function
                | [] -> Pp.Pp.pp exp
                | hd :: tl -> (
                    match hd with
                    | [] -> loop exp tl
                    | hd' :: tl' ->
                        finite_step_aux (leftover_step - 1) (hd', [])
                          (fun e -> App (exp, e))
                          (tl' :: tl))
              in
              loop (ctx (Var x)) arg_stack
          | LLam (x, e) ->
              finite_step_aux (leftover_step - 1)
                (A (LEnv.remove x env', e), [])
                (fun e -> ctx (Lam (x, e)))
                arg_stack
          | LApp (e1, e2) ->
              let e1 = lbl_to_lexp e1 in
              finite_step_aux (leftover_step - 1)
                (A (env', e2), [])
                (fun e -> ctx (App (e1, e)))
                arg_stack)
      | hd :: tl ->
          let exp' = lbl_to_lexp exp' in
          finite_step_aux (leftover_step - 1) (hd, [])
            (fun e -> ctx (App (exp', e)))
            (tl :: arg_stack)

  let finite_step steps pgm =
    let () = print_endline "=========\nInput pgm\n=========" in
    let () =
      Pp.Pp.pp pgm;
      print_newline ()
    in
    let exp = label pgm in
    let () = print_endline "===========\nPartial pgm\n===========" in
    finite_step_aux steps (A (LEnv.empty, exp), []) (fun x -> x) [];
    print_newline ()
end
