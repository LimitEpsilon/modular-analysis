open Syntax

let print_iter = ref false

type time_without_label = string * stx list
type time = time_without_label * int
type 't valSet = 't expr_value Set.t
type 't memory = ('t, 't valSet) Map.t
type 't state = 't ctx * 't
type 't config = tm * 't state
type 't result = 't value * 't
type 't resSet = 't result Set.t
type 't cfSet = 't config Set.t
type 't cache = ('t config, 't resSet) Map.t
type 't tick = 't ctx -> 't -> string -> 't expr_value -> 't

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

let print_state string_of_time (c, t) =
  let to_print = string_of_ctx string_of_time c ^ ", " ^ string_of_time t in
  print_string to_print

let print_result string_of_time (v, t) =
  let to_print =
    "(" ^ string_of_val string_of_time v ^ ", " ^ string_of_time t ^ ")"
  in
  print_string to_print

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

let print_cache string_of_time (a : 't cache) =
  Map.iter
    (fun (e, cf) res ->
      print_string ("(" ^ string_of_tm e ^ ", ");
      print_state string_of_time cf;
      print_string ")";
      print_string "|->";
      print_resset string_of_time res;
      print_newline ())
    a

let rev_mem : (time, time cfSet) Hashtbl.t = Hashtbl.create 10
let dep_graph : (time config, time cfSet) Hashtbl.t = Hashtbl.create 10
let worklist : time config Set.t ref = ref Set.empty
let add_worklist cf = worklist := Set.add cf !worklist

let pop_worklist () =
  match Set.choose_opt !worklist with
  | None -> None
  | Some elt ->
    worklist := Set.remove elt !worklist;
    Some elt

(* add deps: if dep is changed, update cf *)
let update_dep dep cf =
  let original =
    match Hashtbl.find_opt dep_graph dep with
    | Some original -> original
    | None -> Set.empty
  in
  Hashtbl.replace dep_graph dep (Set.add cf original)

(* add deps: if t is changed, update cf *)
let update_rev t cf =
  let original =
    match Hashtbl.find_opt rev_mem t with
    | Some original -> original
    | None -> Set.empty
  in
  Hashtbl.replace rev_mem t (Set.add cf original)

(* cf is changed, add deps to worklist *)
let update_worklist_cf cf =
  let to_add =
    match Hashtbl.find_opt dep_graph cf with
    | Some to_add -> to_add
    | None -> Set.empty
  in
  worklist := Set.union to_add !worklist

(* t is changed, add deps to worklist *)
let update_worklist_t t =
  let to_add =
    match Hashtbl.find_opt rev_mem t with
    | Some to_add -> to_add
    | None -> Set.empty
  in
  worklist := Set.union to_add !worklist

let update_mem t vs (m : 't memory) =
  let changed = ref false in
  let updated =
    Map.update t
      (function
        | None ->
          changed := true;
          Some vs
        | Some vals ->
          let vals' = Set.union vs vals in
          changed := Set.cardinal vals' <> Set.cardinal vals;
          Some vals')
      m
  in
  if !changed then update_worklist_t t;
  updated

(* let compare_mem (m1 : 't memory) (m2 : 't memory) =
     Map.compare Set.compare m1 m2

   let union_mem (m1 : 't memory) (m2 : 't memory) : 't memory =
     Map.union (fun _ r1 r2 -> Some (Set.union r1 r2)) m1 m2 *)

let update_cache (e, s) rs (a : 't cache) =
  let changed = ref false in
  let updated =
    Map.update (e, s)
      (function
        | None ->
          changed := true;
          Some rs
        | Some res ->
          let res' = Set.union rs res in
          changed := Set.cardinal res' <> Set.cardinal res;
          Some res')
      a
  in
  if !changed then update_worklist_cf (e, s);
  updated

(* let compare_cache (a1 : 't cache) (a2 : 't cache) =
     Map.compare Set.compare a1 a2

   let union_cache (a1 : 't cache) (a2 : 't cache) : 't cache =
     Map.union (fun _ r1 r2 -> Some (Set.union r1 r2)) a1 a2 *)

let eval_cache (e : tm) (s : 't state) (a : 't cache) (m : 't memory)
    (tick : 't tick) =
  let c, t = s in
  match e with
  | EVar x -> (
    match addr_x c x with
    | None -> (a, m)
    | Some addr -> (
      update_rev addr (e, s);
      match Map.find_opt addr m with
      | None -> (a, m)
      | Some vals ->
        let results =
          Set.of_list (List.map (fun v -> (EVal v, t)) (Set.elements vals))
        in
        let updated = update_cache (e, s) results a in
        (updated, m)))
  | Lam (x, e') ->
    let result = Set.singleton (EVal (Closure (x, e', c)), t) in
    let updated = update_cache (e, s) result a in
    (updated, m)
  | App (e1, e2) -> (
    update_dep (e1, s) (e, s);
    match Map.find_opt (e1, s) a with
    | None ->
      add_worklist (e1, s);
      let updated = update_cache (e1, s) Set.empty a in
      (updated, m)
    | Some res ->
      Set.fold
        (fun res (acc, m) ->
          match res with
          | EVal (Closure (x, e_lam, c_lam)), t' -> (
            update_dep (e2, (c, t')) (e, s);
            match Map.find_opt (e2, (c, t')) a with
            | None ->
              add_worklist (e2, (c, t'));
              let updated = update_cache (e2, (c, t')) Set.empty acc in
              (updated, m)
            | Some res ->
              Set.fold
                (fun res (acc, m) ->
                  match res with
                  | EVal v, t'' -> (
                    let t''' = tick c t'' x v in
                    let m = update_mem t''' (Set.singleton v) m in
                    let c''' = Cbinde (x, t''', c_lam) in
                    let s''' = (c''', t''') in
                    update_dep (e_lam, s''') (e, s);
                    match Map.find_opt (e_lam, s''') a with
                    | None ->
                      add_worklist (e_lam, s''');
                      let updated = update_cache (e_lam, s''') Set.empty acc in
                      (updated, m)
                    | Some res ->
                      let updated = update_cache (e, s) res acc in
                      (updated, m))
                  | _ -> (acc, m))
                res (acc, m))
          | _ -> (acc, m))
        res (a, m))
  | LetRec (f, x, e1, e2) -> (
    let t' = tick c t f (Closure (x, e1, c)) in
    let v = (Closure (x, e1, Cbinde (f, t', c))) in
    let m = update_mem t' (Set.singleton v) m in
    let c' = Cbinde (f, t', c) in
    let s' = (c', t') in
    update_dep (e2, s') (e, s);
    match Map.find_opt (e2, s') a with
    | None ->
      add_worklist (e2, s');
      let updated = update_cache (e2, s') Set.empty a in
      (updated, m)
    | Some res ->
      let updated = update_cache (e, s) res a in
      (updated, m))
  | Link (e1, e2) -> (
    update_dep (e1, s) (e, s);
    match Map.find_opt (e1, s) a with
    | None ->
      add_worklist (e1, s);
      let updated = update_cache (e1, s) Set.empty a in
      (updated, m)
    | Some res ->
      Set.fold
        (fun res (acc, m) ->
          match res with
          | MVal c', t' -> (
            let s' = (c', t') in
            update_dep (e2, s') (e, s);
            match Map.find_opt (e2, s') a with
            | None ->
              add_worklist (e2, s');
              let updated = update_cache (e2, s') Set.empty acc in
              (updated, m)
            | Some res ->
              let updated = update_cache (e, s) res acc in
              (updated, m))
          | _ -> (acc, m))
        res (a, m))
  | Empty ->
    let result = Set.singleton (MVal c, t) in
    let updated = update_cache (e, s) result a in
    (updated, m)
  | MVar mv -> (
    match ctx_M c mv with
    | None -> (a, m)
    | Some cm ->
      let result = Set.singleton (MVal cm, t) in
      let updated = update_cache (e, s) result a in
      (updated, m))
  | Lete (x, e1, e2) -> (
    match Map.find_opt (e1, s) a with
    | None ->
      add_worklist (e1, s);
      let updated = update_cache (e1, s) Set.empty a in
      (updated, m)
    | Some res ->
      Set.fold
        (fun res (acc, m) ->
          match res with
          | EVal v, t' -> (
            let t'' = tick c t' x v in
            let m = update_mem t'' (Set.singleton v) m in
            let c'' = Cbinde (x, t'', c) in
            let s'' = (c'', t'') in
            update_dep (e2, s'') (e, s);
            match Map.find_opt (e2, s'') a with
            | None ->
              add_worklist (e2, s'');
              let updated = update_cache (e2, s'') Set.empty acc in
              (updated, m)
            | Some res ->
              let updated = update_cache (e, s) res acc in
              (updated, m))
          | _ -> (acc, m))
        res (a, m))
  | Letm (mv, e1, e2) -> (
    update_dep (e1, s) (e, s);
    match Map.find_opt (e1, s) a with
    | None ->
      add_worklist (e1, s);
      let updated = update_cache (e1, s) Set.empty a in
      (updated, m)
    | Some res ->
      Set.fold
        (fun res (acc, m) ->
          match res with
          | MVal cm, t' -> (
            let c' = Cbindm (mv, cm, c) in
            let s' = (c', t') in
            update_dep (e2, s') (e, s);
            match Map.find_opt (e2, s') a with
            | None ->
              add_worklist (e2, s');
              let updated = update_cache (e2, s') Set.empty acc in
              (updated, m)
            | Some res ->
              let updated = update_cache (e, s) res acc in
              (updated, m))
          | _ -> (acc, m))
        res (a, m))

let rec fix (count : int) (cache : 't cache) (mem : 't memory) tick =
  let () =
    if !print_iter then (
      let to_print = "Iteration #" ^ string_of_int count in
      let to_print =
        to_print ^ " Worklist size: " ^ string_of_int (Set.cardinal !worklist)
      in
      print_string to_print;
      print_newline ())
  in
  let old_worklist = !worklist in
  worklist := Set.empty;
  let cache', mem' =
    Set.fold
      (fun (e, s) (a, m) -> eval_cache e s a m tick)
      old_worklist (cache, mem)
  in
  if Set.is_empty !worklist then (cache', mem')
  else fix (count + 1) cache' mem' tick
