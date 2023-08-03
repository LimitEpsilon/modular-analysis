open Syntax

let print_iter = ref false

type 't valSet = 't expr_value Set.t
type 't memory = ('t, 't valSet) Map.t
type 't state = 't ctx * 't
type 't config = tm * 't state
type 't result = 't value * 't
type 't resSet = 't result Set.t
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

let union_mem (m1 : 't memory) (m2 : 't memory) : 't memory =
  Map.union (fun _ r1 r2 -> Some (Set.union r1 r2)) m1 m2

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

let compare_cache (a1 : 't cache) (a2 : 't cache) =
  Map.compare Set.compare a1 a2

let union_cache (a1 : 't cache) (a2 : 't cache) : 't cache =
  Map.union (fun _ r1 r2 -> Some (Set.union r1 r2)) a1 a2

let changed = ref false

let eval_cache (e : tm) (s : 't state) (a : 't cache) (m : 't memory) (tick : 't tick) =
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
          Set.of_list (List.map (fun v -> (EVal v, t)) (Set.elements vals))
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
  let () =
    if !print_iter then (
      let to_print = "Iteration #" ^ string_of_int count in
      print_string to_print;
      print_newline ())
  in
  let updated, updated_mem =
    Map.fold
      (fun (e, s) _ (acc, mem) -> eval_cache e s acc mem tick)
      init (init, mem)
  in
  if not !changed then (init, mem) else fix (count + 1) updated updated_mem tick

let rec filter_ctx_bf (type bf af) (c : ('bf, 'af) link ctx) : 'bf ctx =
  match c with
  | Chole -> Chole
  | Cbinde (_, AF _, c) -> filter_ctx_bf c
  | Cbinde (x, BF t, c) -> Cbinde (x, t, filter_ctx_bf c)
  | Cbindm (m, cm, c) -> Cbindm (m, filter_ctx_bf cm, filter_ctx_bf c)

let filter_v_bf (type bf af) (v : ('bf, 'af) link expr_value) : 'bf expr_value =
  match v with Closure (x, e, c) -> Closure (x, e, filter_ctx_bf c)

let rec filter_ctx_af (type bf af) (c : ('bf, 'af) link ctx) : 'af ctx =
  match c with
  | Chole -> Chole
  | Cbinde (_, BF _, c) -> filter_ctx_af c
  | Cbinde (x, AF t, c) -> Cbinde (x, t, filter_ctx_af c)
  | Cbindm (m, cm, c) -> Cbindm (m, filter_ctx_af cm, filter_ctx_af c)

let filter_v_af (type bf af) (v : ('bf, 'af) link expr_value) : 'af expr_value =
  match v with Closure (x, e, c) -> Closure (x, e, filter_ctx_af c)

let rec lift_ctx_bf (type bf af) (c : 'bf ctx) : ('bf, 'af) link ctx =
  match c with
  | Chole -> Chole
  | Cbinde (x, t, c) -> Cbinde (x, BF t, lift_ctx_bf c)
  | Cbindm (m, cm, c) -> Cbindm (m, lift_ctx_bf cm, lift_ctx_bf c)

let lift_ev_bf (type bf af) (ev : 'bf expr_value) : ('bf, 'af) link expr_value =
  match ev with Closure (x, e, c) -> Closure (x, e, lift_ctx_bf c)

let lift_v_bf (type bf af) (v : 'bf value) : ('bf, 'af) link value =
  match v with
  | EVal ev -> EVal (lift_ev_bf ev)
  | MVal c -> MVal (lift_ctx_bf c)

let lift_s_bf (type bf af) (s : 'bf state) : ('bf, 'af) link state =
  match s with c, t -> (lift_ctx_bf c, BF t)

let lift_cf_bf (type bf af) (cf : 'bf config) : ('bf, 'af) link config =
  match cf with e, s -> (e, lift_s_bf s)

let lift_vs_bf (type bf af) (vs : 'bf valSet) : ('bf, 'af) link valSet =
  let vs = Set.elements vs in
  let vs = List.map lift_ev_bf vs in
  Set.of_list vs

let lift_rs_bf (type bf af) (rs : 'bf resSet) : ('bf, 'af) link resSet =
  let rs = Set.elements rs in
  let rs = List.map (fun (v, t) -> (lift_v_bf v, BF t)) rs in
  Set.of_list rs

let lift_mem_bf (type bf af) (m : 'bf memory) : ('bf, 'af) link memory =
  let m = Map.to_list m in
  let m = List.map (fun (t, vs) -> (BF t, lift_vs_bf vs)) m in
  Map.of_list m

let lift_cache_bf (type bf af) (a : 'bf cache) : ('bf, 'af) link cache =
  let a = Map.to_list a in
  let a = List.map (fun (cf, rs) -> (lift_cf_bf cf, lift_rs_bf rs)) a in
  Map.of_list a

let rec lift_ctx_af (type bf af) (c : 'af ctx) : ('bf, 'af) link ctx =
  match c with
  | Chole -> Chole
  | Cbinde (x, t, c) -> Cbinde (x, AF t, lift_ctx_af c)
  | Cbindm (m, cm, c) -> Cbindm (m, lift_ctx_af cm, lift_ctx_af c)

let lift_ev_af (type bf af) (ev : 'af expr_value) : ('bf, 'af) link expr_value =
  match ev with Closure (x, e, c) -> Closure (x, e, lift_ctx_af c)

let lift_v_af (type bf af) (v : 'af value) : ('bf, 'af) link value =
  match v with
  | EVal ev -> EVal (lift_ev_af ev)
  | MVal c -> MVal (lift_ctx_af c)

let lift_s_af (type bf af) (s : 'af state) : ('bf, 'af) link state =
  match s with c, t -> (lift_ctx_af c, AF t)

let lift_cf_af (type bf af) (cf : 'af config) : ('bf, 'af) link config =
  match cf with e, s -> (e, lift_s_af s)

let lift_vs_af (type bf af) (vs : 'af valSet) : ('bf, 'af) link valSet =
  let vs = Set.elements vs in
  let vs = List.map lift_ev_af vs in
  Set.of_list vs

let lift_rs_af (type bf af) (rs : 'af resSet) : ('bf, 'af) link resSet =
  let rs = Set.elements rs in
  let rs = List.map (fun (v, t) -> (lift_v_af v, AF t)) rs in
  Set.of_list rs

let lift_mem_af (type bf af) (m : 'af memory) : ('bf, 'af) link memory =
  let m = Map.to_list m in
  let m = List.map (fun (t, vs) -> (AF t, lift_vs_af vs)) m in
  Map.of_list m

let lift_cache_af (type bf af) (a : 'af cache) : ('bf, 'af) link cache =
  let a = Map.to_list a in
  let a = List.map (fun (cf, rs) -> (lift_cf_af cf, lift_rs_af rs)) a in
  Map.of_list a

let inject_ev (c : 't ctx) (ev : 't expr_value) =
  match ev with Closure (x, e, c') -> Closure (x, e, inject_ctx c c')

let inject_v (c : 't ctx) (v : 't value) =
  match v with
  | EVal ev -> EVal (inject_ev c ev)
  | MVal c' -> MVal (inject_ctx c c')

let inject_s (c : 't ctx) (s : 't state) =
  match s with c', t -> (inject_ctx c c', t)

let inject_cf (c : 't ctx) (cf : 't config) =
  match cf with e, s -> (e, inject_s c s)

let inject_vs (c : 't ctx) (vs : 't valSet) = Set.map (inject_ev c) vs

let inject_rs (c : 't ctx) (rs : 't resSet) =
  Set.map (fun (v, t) -> (inject_v c v, t)) rs

let inject_mem (c : 't ctx) (m : 't memory) = Map.map (inject_vs c) m

let inject_cache (c : 't ctx) (a : 't cache) =
  let a = Map.to_list a in
  let a = List.map (fun (cf, rs) -> (inject_cf c cf, inject_rs c rs)) a in
  Map.of_list a

let link_one (type bf af) (bf_c : ('bf, 'af) link ctx)
    (af_cache : ('bf, 'af) link cache) (mem : ('bf, 'af) link memory)
    (tick : 'af tick) =
  let link_tick c t x v =
    match t with
    | BF _ -> t
    | AF t ->
      let t' =
        match v with
        | Closure (x', e', c') ->
          tick
            (filter_ctx_af (delete_ctx bf_c c))
            t x
            (Closure (x', e', filter_ctx_af (delete_ctx bf_c c')))
      in
      AF t'
  in
  let cache = inject_cache bf_c af_cache in
  fix 0 cache mem link_tick

let init_cf (init : 't) e : 't config = (e, (Chole, init))

let init_cache (init : 't) e : 't cache =
  Map.add (init_cf init e) Set.empty Map.empty

let link (init_bf : 'bf) (init_af : 'af) (tick_bf : 'bf tick)
    (tick_af : 'af tick) e1 e2 =
  let bf_cache, bf_mem = fix 0 (init_cache init_bf e1) Map.empty tick_bf in
  let af_cache, af_mem = fix 0 (init_cache init_af e2) Map.empty tick_af in
  let bf_cache = lift_cache_bf bf_cache in
  let bf_mem = lift_mem_bf bf_mem in
  let af_cache = lift_cache_af af_cache in
  let af_mem = lift_mem_af af_mem in
  let export =
    Set.fold
      (fun res acc -> match res with MVal c, _ -> c :: acc | _ -> acc)
      (Map.find (init_cf (BF init_bf) e1) bf_cache)
      []
  in
  let cache, mem, res =
    List.fold_left
      (fun (acc_cache, acc_mem, acc_res) c ->
        let init = (e2, (c, AF init_af)) in
        let link_mem = union_mem bf_mem (inject_mem c af_mem) in
        let cache, mem = link_one c af_cache link_mem tick_af in
        let res = Map.find init cache in
        ( union_cache acc_cache cache,
          union_mem acc_mem mem,
          Set.union acc_res res ))
      (bf_cache, bf_mem, Set.empty)
      export
  in
  let cache, _ =
    update_cache (init_cf (BF init_bf) (Link (e1, e2))) res cache
  in
  (cache, mem)
