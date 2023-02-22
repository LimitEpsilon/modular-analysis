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

  (* invariant: only initial labels go into the environment *)
  let rec step (A (env, exp) : t) : t =
    match Hashtbl.find label_table exp with
    | LVar x -> (
        match LEnv.find x env with
        | exception Not_found -> A (env, exp)
        | A (env, exp) -> step (A (env, exp)))
    | LLam (_, _) -> A (env, exp)
    | LApp (e1, e2) -> (
        let (A (new_env, lam)) = step (A (env, e1)) in
        match Hashtbl.find label_table lam with
        | LLam (x, e) ->
            let updated_env =
              LEnv.update x (fun _ -> Some (A (env, e2))) new_env
            in
            step (A (updated_env, e))
        | _ ->
            let lbl =
              incr num_of_lbls;
              !num_of_lbls
            in
            Hashtbl.add label_table lbl (LApp (lam, e2));
            A (env, lbl))

  let rec reduce (A (env, exp) : t) : lexp =
    let (A (env', exp')) = step (A (env, exp)) in
    match Hashtbl.find label_table exp' with
    | LVar x -> Var x
    | LLam (x, e) -> Lam (x, reduce (A (LEnv.remove x env', e)))
    | LApp (e1, e2) -> App (lbl_to_lexp e1, reduce (A (env', e2)))

  let reduce_lexp e =
    let my_lbl = label e in
    let original_lbls = !num_of_lbls in
    let reduced = reduce (A (LEnv.empty, my_lbl)) in
    print_string
      ("Number of syntactic locations: "
      ^ string_of_int original_lbls
      ^ "\nNumber of added locations: " ^ string_of_int !num_of_lbls ^ "\n");
    reduced
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

  let rec finite_step_aux leftover_step to_eval =
    if leftover_step < 0 then print to_eval
    else finite_step_aux (leftover_step - 1) (step to_eval)

  let finite_step steps pgm =
    let exp = label pgm in
    finite_step_aux steps (A (LEnv.empty, exp))
end
