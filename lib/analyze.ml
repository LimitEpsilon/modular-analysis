open Syntax

let pp e = print_string (string_of_tm e)

module type Time = sig
  type t
  val tick : t ctx -> t -> string -> t expr_value -> t
  val string_of_time : t -> string
end

module Dom (T : sig 
  type t 
  val string_of_time : t -> string
end) = struct
  module Mem = Map.Make(struct
    type t = T.t
    let compare = compare
  end)
  module ValSet = Set.Make(struct
    type t = T.t expr_value
    let compare = compare
  end)
  type context = T.t ctx (* type of my ctx *)
  type memory = ValSet.t Mem.t (* type of my memory *)
  type config = context * T.t
  type result = T.t value * T.t

  let rec string_of_ctx c =
    match c with
    | Chole -> "[]"
    | Cbinde (x, t, c) ->
      "\\" ^ x ^ ":" ^ T.string_of_time t ^ "." ^ string_of_ctx c
    | Cbindm (m, cm, c) ->
      "\\" ^ m ^ ":" ^ string_of_ctx cm ^ "." ^ string_of_ctx c

  let string_of_ev ev =
    match ev with
    | Closure (x, e, c) -> 
      "<\\" ^ x ^ "." ^ string_of_tm e ^ ", " ^ string_of_ctx c ^ ">"

  let string_of_val v =
    match v with
    | EVal v -> string_of_ev v
    | MVal c -> string_of_ctx c

  let print_valset (vs : ValSet.t) =
    let vl = ValSet.elements vs in
    print_string "{";
    (match vl with
    | [] -> ()
    | v :: tl -> 
      print_string (string_of_ev v);
      List.iter (fun v -> print_string (", " ^ string_of_ev v)) tl
    ); print_string "}" 
  
  let print_mem (m : memory) =
    let first = ref true in
    Mem.iter (fun t vals ->
      (if !first then first := false else print_string "U");
      print_string ("[" ^ T.string_of_time t ^ "|->");
      print_valset vals;
      print_string "]") m

  let print_config (c, t) =
    let to_print = string_of_ctx c ^ ", " ^ T.string_of_time t in
    print_string to_print
  
  let print_result (v, t) =
    let to_print = "(" ^ string_of_val v ^ ", " ^ T.string_of_time t ^ ")" in
    print_string to_print

  let update_mem t vs (m : memory) =
    let changed = ref false in
    let updated = Mem.update t 
      (function
      | None -> changed := true; Some vs
      | Some vals -> 
        let diff = ValSet.diff vs vals in
        changed := not (ValSet.is_empty diff);
        Some (ValSet.union diff vals)) m in
    (updated, !changed)
  
  let compare_mem m1 m2 = Mem.compare ValSet.compare m1 m2

  module ResSet = Set.Make(struct
    type t = result
    let compare = compare
  end)
  module Cache = Map.Make (struct
    type t = tm * config
    let compare = compare
  end)

  let print_resset (vs : ResSet.t) =
    let vl = ResSet.elements vs in
    print_string "{";
    (match vl with
    | [] -> ()
    | r :: tl -> 
      print_result r;
      List.iter (fun r -> print_string ", "; print_result r) tl
    ); print_string "}" 

  type cache = ResSet.t Cache.t
  let update_cache (e, s) rs (a : cache) =
    let changed = ref false in
    let updated = Cache.update (e, s) 
      (function
      | None -> changed := true; Some rs
      | Some res ->
        let diff = ResSet.diff rs res in
        changed := not (ResSet.is_empty diff);
        Some (ResSet.union diff res)) a in
    (updated, !changed)
  
  let compare_cache = Cache.compare ResSet.compare

  let union_cache (a1 : cache) (a2 : cache) =
    Cache.union (fun _ r1 r2 -> Some (ResSet.union r1 r2)) a1 a2

  let print_cache (a : cache) =
    Cache.iter (fun (e, cf) res ->
      print_string "(";
      pp e;
      print_string ", ";
      print_config cf;
      print_string ")";
      print_string "|->";
      print_resset res;
      print_newline ()) a
end

module Analyzer (T : Time) = struct
  module Dom = Dom(T)
  open Dom
  let changed = ref false
  let eval_cache (e : tm) (s : config) (a : cache) (m : memory)  =
    let (c, t) = s in
    match e with
    | EVar x -> (
      match addr_x c x with
      | None -> (a, m)
      | Some addr -> (
        match Mem.find_opt addr m with
        | None -> (a, m)
        | Some vals ->
          let results = 
            ResSet.of_list 
            (List.map (fun v -> (EVal v, t)) (ValSet.elements vals)) in
          let updated, changed' = update_cache (e, s) results a in
          changed := !changed || changed';
          (updated, m)))
    | Lam (x, e') -> 
      let result = ResSet.singleton (EVal (Closure (x, e', c)), t) in
      let updated, changed' = update_cache (e, s) result a in
      changed := !changed || changed';
      (updated, m)
    | App (e1, e2) -> (
      match Cache.find_opt (e1, s) a with
      | None ->
        let updated, changed' = update_cache (e1, s) ResSet.empty a in
        changed := !changed || changed';
        (updated, m)
      | Some res ->
        ResSet.fold (fun res (acc, m) ->
        match res with
        | (EVal (Closure (x, e_lam, c_lam)), t') ->
          (match Cache.find_opt (e2, (c, t')) a with
          | None ->
            let updated, changed' = update_cache (e2, (c, t')) ResSet.empty acc in
            changed := !changed || changed';
            (updated, m)
          | Some res ->
            ResSet.fold (fun res (acc, m) ->
            match res with
            | (EVal v, t'') -> (
              let t''' = T.tick c t'' x v in
              let m, changed' = update_mem t'' (ValSet.singleton v) m in
              let () = changed := !changed || changed' in
              let c''' = plugin c_lam (Cbinde (x, t'', Chole)) in
              let s''' = (c''', t''') in
              match Cache.find_opt (e_lam, s''') a with
              | None -> 
                let () = print_string (string_of_ctx c); print_newline () in
                let updated, changed' = update_cache (e_lam, s''') ResSet.empty acc in
                changed := !changed || changed';
                (updated, m)
              | Some res -> (
                let updated, changed' = update_cache (e, s) res acc in
                changed := !changed || changed';
                (updated, m)))
            | _ -> (acc, m)) res (acc, m))
        | _ -> (acc, m)) res (a, m))
    | Link (e1, e2) -> (
      match Cache.find_opt (e1, s) a with
      | None -> 
        let updated, changed' = update_cache (e1, s) ResSet.empty a in
        changed := !changed || changed';
        (updated, m)
      | Some res ->
        ResSet.fold (fun res (acc, m) ->
        match res with
        | (MVal c', t') ->
          let s' = (c', t') in
          (match Cache.find_opt (e2, s') a with
          | None -> 
            let updated, changed' = update_cache (e2, s') ResSet.empty acc in
            changed := !changed || changed';
            (updated, m)
          | Some res -> 
            let updated, changed' = update_cache (e, s) res acc in
            changed := !changed || changed';
            (updated, m))
        | _ -> (acc, m)) res (a, m))
    | Empty -> 
      let result = ResSet.singleton (MVal c, t) in
      let updated, changed' = update_cache (e, s) result a in
      changed := !changed || changed';
      (updated, m)
    | MVar mv -> (
      match ctx_M c mv with
      | None -> (a, m)
      | Some cm -> 
        let result = ResSet.singleton (MVal cm, t) in
        let updated, changed' = update_cache (e, s) result a in
        changed := !changed || changed';
        (updated, m))
    | Lete (x, e1, e2) -> (
      match Cache.find_opt (e1, s) a with
      | None -> 
        let updated, changed' = update_cache (e1, s) ResSet.empty a in
        changed := !changed || changed';
        (updated, m)
      | Some res ->
        ResSet.fold (fun res (acc, m) ->
        match res with
        | (EVal v, t') ->
          let t'' = T.tick c t' x v in
          let m, changed' = update_mem t' (ValSet.singleton v) m in
          let () = changed := !changed || changed' in
          let c'' = plugin c (Cbinde (x, t', Chole)) in
          let s'' = (c'', t'') in
          (match Cache.find_opt (e2, s'') a with
          | None -> 
            let updated, changed' = update_cache (e2, s'') ResSet.empty acc in
            changed := !changed || changed';
            (updated, m)
          | Some res -> 
            let updated, changed' = update_cache (e, s) res acc in
            changed := !changed || changed';
            (updated, m))
        | _ -> (acc, m)) res (a, m))
    | Letm (mv, e1, e2) -> (
      match Cache.find_opt (e1, s) a with
      | None -> 
        let updated, changed' = update_cache (e1, s) ResSet.empty a in
        changed := !changed || changed';
        (updated, m)
      | Some res ->
        ResSet.fold (fun res (acc, m) ->
        match res with
        | (MVal cm, t') ->
          let c' = plugin c (Cbindm (mv, cm, Chole)) in
          let s' = (c', t') in
          (match Cache.find_opt (e2, s') a with
          | None -> 
            let updated, changed' = update_cache (e2, s') ResSet.empty acc in
            changed := !changed || changed';
            (updated, m)
          | Some res -> 
            let updated, changed' = update_cache (e, s) res acc in
            changed := !changed || changed';
            (updated, m))
        | _ -> (acc, m)) res (a, m))
  
  let rec fix (count : int) (init : cache) (mem : memory) =
    let () = changed := false in
    let to_print = "Iteration #" ^ (string_of_int count) ^ "\n" in
    let () = print_string to_print in
    let updated, updated_mem = 
      Cache.fold
      (fun (e, s) _ (acc, mem) -> eval_cache e s acc mem)
      init (init, mem) in
    if not !changed then (init, mem) else fix (count + 1) updated updated_mem
end
