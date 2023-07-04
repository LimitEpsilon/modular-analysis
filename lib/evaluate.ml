open Lambda

let rec pp exp =
    match exp with
    | EVar s
    | MVar s -> print_string s
    | Lam (s, e) ->
        print_string "\\";
        print_string (s ^ ".");
        pp e;
        print_string ""
    | App (e1, e2) ->
        print_string "(";
        pp e1;
        print_string ") (";
        pp e2;
        print_string ")"
    | Link (e1, e2) ->
        print_string "(";
        pp e1;
        print_string ")!(";
        pp e2;
        print_string ")"
    | Empty -> print_string "ε"
    | Lete (x, e1, e2)
    | Letm (x, e1, e2) ->
      print_string "let ";
      print_string x;
      print_string " = ";
      pp e1;
      print_string " in ";
      pp e2

module type Time = sig
  type t
  val tick : t ctx -> t -> string -> t expr_value -> t
  val print : t -> unit
end

module Dom (T : sig 
  type t 
  val print : t -> unit
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
  type config = context * memory * T.t
  type result = T.t value * memory * T.t

  let rec print_ctx c =
    match c with
    | Hole -> print_string "[]"
    | CLam (x, t, c) -> 
      print_string "\\";
      print_string x;
      print_string ":";
      T.print t;
      print_string ".";
      print_ctx c
    | CLete (x, t, c) ->
      print_string "let ";
      print_string x;
      print_string ":";
      T.print t;
      print_string " in ";
      print_ctx c
    | CLetm (m, cm, c) ->
      print_string "let ";
      print_string m;
      print_string ":(";
      print_ctx cm;
      print_string ")";
      print_string " in ";
      print_ctx c

  let print_expr_value v =
    match v with
    | Closure (x, e, c) ->
      print_string "<\\";
      print_string x;
      print_string ".";
      pp e;
      print_string ", ";
      print_ctx c;
      print_string ">"

  let print_value v =
    match v with
    | EVal v -> print_expr_value v
    | MVal c -> print_ctx c

  let print_valset (vs : ValSet.t) =
    let vl = ValSet.elements vs in
    print_string "{";
    (match vl with
    | [] -> ()
    | v :: tl -> 
      print_expr_value v;
      List.iter (fun v -> print_string ", "; print_expr_value v) tl
    ); print_string "}" 
  
  let print_mem (m : memory) =
    let first = ref true in
    Mem.iter (fun t vals ->
      (if !first then first := false else print_string "U");
      print_string "[";
      T.print t;
      print_string "|->";
      print_valset vals;
      print_string "]") m

  let print_config (c, m, t) =
    print_ctx c;
    print_string ", ";
    print_mem m;
    print_string ", ";
    T.print t
  
  let print_result (v, m, t) =
    print_string "(";
    print_value v;
    print_string ", ";
    print_mem m;
    print_string ", ";
    T.print t;
    print_string ")"

  let update_mem t vs (m : memory) =
    Mem.update t 
      (function
      | None -> Some vs
      | Some vals -> Some (ValSet.union vals vs)) m
  
  let compare_res r1 r2 =
    match (r1, r2) with
    | (v1, m1, t1), (v2, m2, t2) ->
      let compv = compare v1 v2 in
      let compm = Mem.compare ValSet.compare m1 m2 in
      let compt = compare t1 t2 in
      if compv < 0 then -1
      else if compv > 0 then 1
      else if compm < 0 then -1
      else if compm > 0 then 1
      else if compt < 0 then -1
      else if compt > 0 then 1
      else 0
  
  module ResSet = Set.Make(struct
    type t = result
    let compare = compare_res
  end)
  module Cache = Map.Make (struct
    type t = tm * config
    let compare (e1, s1) (e2, s2) =
      let compe = compare e1 e2 in
      let comps = compare_res s1 s2 in
      if compe < 0 then -1
      else if compe > 0 then 1
      else if comps < 0 then -1
      else if comps > 0 then 1
      else 0
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
    Cache.update (e, s) 
      (function
      | None -> Some rs
      | Some res -> Some (ResSet.union res rs)) a
  
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
  let eval_cache (e : tm) (s : config) (a : cache) =
    let delta = Cache.empty in
    let (c, m, t) = s in
    match e with
    | EVar x -> (
      match addr_x c x with
      | None -> delta
      | Some addr -> (
        match Mem.find_opt addr m with
        | None -> delta
        | Some vals ->
          let results = 
            ResSet.of_list 
            (List.map (fun v -> (EVal v, m, t)) (ValSet.elements vals))
          in update_cache (e, s) results delta))
    | Lam (x, e') -> 
      let result = ResSet.singleton (EVal (Closure (x, e', c)), m, t) in
      update_cache (e, s) result delta
    | App (e1, e2) -> (
      match Cache.find_opt (e1, s) a with
      | None -> update_cache (e1, s) ResSet.empty delta
      | Some res ->
        ResSet.fold (fun res acc ->
        match res with
        | (EVal (Closure (x, e_lam, c_lam)), m', t') ->
          (match Cache.find_opt (e2, (c, m', t')) a with
          | None -> update_cache (e2, (c, m', t')) ResSet.empty acc
          | Some res ->
            ResSet.fold (fun res acc ->
            match res with
            | (EVal v, m'', t'') -> (
              let t''' = T.tick c t'' x v in
              let m''' = update_mem t'' (ValSet.singleton v) m'' in
              let c''' = plugin c_lam (CLam (x, t'', Hole)) in
              let s''' = (c''', m''', t''') in
              match Cache.find_opt (e_lam, s''') a with
              | None -> update_cache (e_lam, s''') ResSet.empty acc
              | Some res -> update_cache (e, s) res acc)
            | _ -> acc) res acc) 
        | _ -> acc) res delta)
    | Link (e1, e2) -> (
      match Cache.find_opt (e1, s) a with
      | None -> update_cache (e1, s) ResSet.empty delta
      | Some res ->
        ResSet.fold (fun res acc ->
        match res with
        | (MVal c', m', t') ->
          let s' = (c', m', t') in
          (match Cache.find_opt (e2, s') a with
          | None -> update_cache (e2, s') ResSet.empty acc
          | Some res -> update_cache (e, s) res acc)
        | _ -> acc) res delta)
    | Empty -> 
      let result = ResSet.singleton (MVal c, m, t) in
      update_cache (e, s) result delta
    | MVar mv -> (
      match ctx_M c mv with
      | None -> delta
      | Some cm -> 
        let result = ResSet.singleton (MVal cm, m, t) in
        update_cache (e, s) result delta)
    | Lete (x, e1, e2) -> (
      match Cache.find_opt (e1, s) a with
      | None -> update_cache (e1, s) ResSet.empty delta
      | Some res ->
        ResSet.fold (fun res acc ->
        match res with
        | (EVal v, m', t') ->
          let t'' = T.tick c t' x v in
          let m'' = update_mem t' (ValSet.singleton v) m' in
          let c'' = plugin c (CLete (x, t', Hole)) in
          let s'' = (c'', m'', t'') in
          (match Cache.find_opt (e2, s'') a with
          | None -> update_cache (e2, s'') ResSet.empty acc
          | Some res -> update_cache (e, s) res acc)
        | _ -> acc) res delta)
    | Letm (mv, e1, e2) -> (
      match Cache.find_opt (e1, s) a with
      | None -> update_cache (e1, s) ResSet.empty delta
      | Some res ->
        ResSet.fold (fun res acc ->
        match res with
        | (MVal cm, m', t') ->
          let c' = plugin c (CLetm (mv, cm, Hole)) in
          let s' = (c', m', t') in
          (match Cache.find_opt (e2, s') a with
          | None -> update_cache (e2, s') ResSet.empty acc
          | Some res -> update_cache (e, s) res acc)
        | _ -> acc) res delta)
  
  let rec fix (init : cache) =
    let delta = 
      Cache.fold 
      (fun (e, s) _ acc -> union_cache acc (eval_cache e s init))
      init Cache.empty in
    let updated = union_cache init delta in
    if (Cache.compare ResSet.compare init updated) = 0
      then init
      else fix updated
end
