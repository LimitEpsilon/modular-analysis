open Syntax

let pp e = print_string (string_of_tm e)

type 't valSet = 't expr_value Set.t
type 't memory = ('t, 't valSet) Map.t
type 't config = 't ctx * 't
type 't result = 't value * 't
type 't resSet = 't result Set.t
type 't cache = (tm * 't config, 't resSet) Map.t

let rec string_of_ctx string_of_time c =
  match c with
  | Chole -> "[]"
  | Cbinde (x, t, c) ->
    "\\" ^ x ^ ":" ^ string_of_time t ^ "." ^ string_of_ctx string_of_time c
  | Cbindm (m, cm, c) ->
    "\\" ^ m ^ ":"
    ^ string_of_ctx string_of_time cm
    ^ "."
    ^ string_of_ctx string_of_time c

let string_of_ev string_of_time ev =
  match ev with
  | Closure (x, e, c) ->
    "<\\" ^ x ^ "." ^ string_of_tm e ^ ", "
    ^ string_of_ctx string_of_time c
    ^ ">"

let string_of_val string_of_time v =
  match v with
  | EVal v -> string_of_ev string_of_time v
  | MVal c -> string_of_ctx string_of_time c

let print_valset string_of_time (vs : 't valSet) =
  let vl = Set.elements vs in
  print_string "{";
  (match vl with
  | [] -> ()
  | v :: tl ->
    print_string (string_of_ev string_of_time v);
    List.iter (fun v -> print_string (", " ^ string_of_ev string_of_time v)) tl);
  print_string "}"

let print_mem string_of_time (m : 't memory) =
  let first = ref true in
  Map.iter
    (fun t vals ->
      if !first then first := false else print_string "U";
      print_string ("[" ^ string_of_time t ^ "|->");
      print_valset string_of_time vals;
      print_string "]")
    m

let print_config string_of_time (c, t) =
  let to_print = string_of_ctx string_of_time c ^ ", " ^ string_of_time t in
  print_string to_print

let print_result string_of_time (v, t) =
  let to_print =
    "(" ^ string_of_val string_of_time v ^ ", " ^ string_of_time t ^ ")"
  in
  print_string to_print

let update_mem t vs (m : 't memory) =
  let changed = ref false in
  let updated =
    Map.update t
      (function
        | None ->
          changed := true;
          Some vs
        | Some vals ->
          let diff = Set.diff vs vals in
          changed := not (Set.is_empty diff);
          Some (Set.union diff vals))
      m
  in
  (updated, !changed)

let compare_mem (m1 : 't memory) (m2 : 't memory) =
  Map.compare Set.compare m1 m2

let print_resset string_of_time (vs : 't resSet) =
  let vl = Set.elements vs in
  print_string "{";
  (match vl with
  | [] -> ()
  | r :: tl ->
    print_result string_of_time r;
    List.iter
      (fun r ->
        print_string ", ";
        print_result string_of_time r)
      tl);
  print_string "}"

let update_cache (e, s) rs (a : 't cache) =
  let changed = ref false in
  let updated =
    Map.update (e, s)
      (function
        | None ->
          changed := true;
          Some rs
        | Some res ->
          let diff = Set.diff rs res in
          changed := not (Set.is_empty diff);
          Some (Set.union diff res))
      a
  in
  (updated, !changed)

let compare_cache (c1 : 't cache) (c2 : 't cache) =
  Map.compare Set.compare c1 c2

let union_cache (a1 : 't cache) (a2 : 't cache) =
  Map.union (fun _ r1 r2 -> Some (Set.union r1 r2)) a1 a2

let print_cache string_of_time (a : 't cache) =
  Map.iter
    (fun (e, cf) res ->
      print_string "(";
      pp e;
      print_string ", ";
      print_config string_of_time cf;
      print_string ")";
      print_string "|->";
      print_resset string_of_time res;
      print_newline ())
    a

let changed = ref false

let eval_cache (e : tm) (s : 't config) (a : 't cache) (m : 't memory) tick =
  let c, t = s in
  match e with
  | EVar x -> (
    match addr_x c x with
    | None -> (a, m)
    | Some addr -> (
      match Map.find_opt addr m with
      | None -> (a, m)
      | Some vals ->
        let results =
          Set.of_list
            (List.map (fun v -> (EVal v, t)) (Set.elements vals))
        in
        let updated, changed' = update_cache (e, s) results a in
        changed := !changed || changed';
        (updated, m)))
  | Lam (x, e') ->
    let result = Set.singleton (EVal (Closure (x, e', c)), t) in
    let updated, changed' = update_cache (e, s) result a in
    changed := !changed || changed';
    (updated, m)
  | App (e1, e2) -> (
    match Map.find_opt (e1, s) a with
    | None ->
      let updated, changed' = update_cache (e1, s) Set.empty a in
      changed := !changed || changed';
      (updated, m)
    | Some res ->
      Set.fold
        (fun res (acc, m) ->
          match res with
          | EVal (Closure (x, e_lam, c_lam)), t' -> (
            match Map.find_opt (e2, (c, t')) a with
            | None ->
              let updated, changed' =
                update_cache (e2, (c, t')) Set.empty acc
              in
              changed := !changed || changed';
              (updated, m)
            | Some res ->
              Set.fold
                (fun res (acc, m) ->
                  match res with
                  | EVal v, t'' -> (
                    let t''' = tick c t'' x v in
                    let m, changed' = update_mem t'' (Set.singleton v) m in
                    let () = changed := !changed || changed' in
                    let c''' = plugin c_lam (Cbinde (x, t'', Chole)) in
                    let s''' = (c''', t''') in
                    match Map.find_opt (e_lam, s''') a with
                    | None ->
                      let updated, changed' =
                        update_cache (e_lam, s''') Set.empty acc
                      in
                      changed := !changed || changed';
                      (updated, m)
                    | Some res ->
                      let updated, changed' = update_cache (e, s) res acc in
                      changed := !changed || changed';
                      (updated, m))
                  | _ -> (acc, m))
                res (acc, m))
          | _ -> (acc, m))
        res (a, m))
  | Link (e1, e2) -> (
    match Map.find_opt (e1, s) a with
    | None ->
      let updated, changed' = update_cache (e1, s) Set.empty a in
      changed := !changed || changed';
      (updated, m)
    | Some res ->
      Set.fold
        (fun res (acc, m) ->
          match res with
          | MVal c', t' -> (
            let s' = (c', t') in
            match Map.find_opt (e2, s') a with
            | None ->
              let updated, changed' = update_cache (e2, s') Set.empty acc in
              changed := !changed || changed';
              (updated, m)
            | Some res ->
              let updated, changed' = update_cache (e, s) res acc in
              changed := !changed || changed';
              (updated, m))
          | _ -> (acc, m))
        res (a, m))
  | Empty ->
    let result = Set.singleton (MVal c, t) in
    let updated, changed' = update_cache (e, s) result a in
    changed := !changed || changed';
    (updated, m)
  | MVar mv -> (
    match ctx_M c mv with
    | None -> (a, m)
    | Some cm ->
      let result = Set.singleton (MVal cm, t) in
      let updated, changed' = update_cache (e, s) result a in
      changed := !changed || changed';
      (updated, m))
  | Lete (x, e1, e2) -> (
    match Map.find_opt (e1, s) a with
    | None ->
      let updated, changed' = update_cache (e1, s) Set.empty a in
      changed := !changed || changed';
      (updated, m)
    | Some res ->
      Set.fold
        (fun res (acc, m) ->
          match res with
          | EVal v, t' -> (
            let t'' = tick c t' x v in
            let m, changed' = update_mem t' (Set.singleton v) m in
            let () = changed := !changed || changed' in
            let c'' = plugin c (Cbinde (x, t', Chole)) in
            let s'' = (c'', t'') in
            match Map.find_opt (e2, s'') a with
            | None ->
              let updated, changed' = update_cache (e2, s'') Set.empty acc in
              changed := !changed || changed';
              (updated, m)
            | Some res ->
              let updated, changed' = update_cache (e, s) res acc in
              changed := !changed || changed';
              (updated, m))
          | _ -> (acc, m))
        res (a, m))
  | Letm (mv, e1, e2) -> (
    match Map.find_opt (e1, s) a with
    | None ->
      let updated, changed' = update_cache (e1, s) Set.empty a in
      changed := !changed || changed';
      (updated, m)
    | Some res ->
      Set.fold
        (fun res (acc, m) ->
          match res with
          | MVal cm, t' -> (
            let c' = plugin c (Cbindm (mv, cm, Chole)) in
            let s' = (c', t') in
            match Map.find_opt (e2, s') a with
            | None ->
              let updated, changed' = update_cache (e2, s') Set.empty acc in
              changed := !changed || changed';
              (updated, m)
            | Some res ->
              let updated, changed' = update_cache (e, s) res acc in
              changed := !changed || changed';
              (updated, m))
          | _ -> (acc, m))
        res (a, m))

let rec fix (count : int) (init : 't cache) (mem : 't memory) tick =
  let () = changed := false in
  let to_print = "Iteration #" ^ string_of_int count ^ "\n" in
  let () = print_string to_print in
  let updated, updated_mem =
    Map.fold
      (fun (e, s) _ (acc, mem) -> eval_cache e s acc mem tick)
      init (init, mem)
  in
  if not !changed then (init, mem) else fix (count + 1) updated updated_mem tick
