type tm = 
  | EVar of string
  | Lam of string * tm
  | App of tm * tm
  | Link of tm * tm
  | Empty
  | MVar of string
  | Lete of string * tm * tm
  | Letm of string * tm * tm

let rec string_of_tm e =
  match e with
  | EVar x
  | MVar x -> x
  | Lam (x, e) ->
    "\\" ^ x ^ "." ^ string_of_tm e
  | App (e1, e2) ->
    "(" ^ string_of_tm e1 ^ ") (" ^ string_of_tm e2 ^ ")"
  | Link (e1, e2) ->
    "(" ^ string_of_tm e1 ^ ")!(" ^ string_of_tm e2 ^ ")"
  | Empty -> "ε"
  | Lete (x, e1, e2)
  | Letm (x, e1, e2) ->
    "let " ^ x ^ " = " ^ string_of_tm e1 ^ " in\n(" ^ string_of_tm e2 ^ ")"

type ('t1, 't2) link =
  | BF of 't1
  | AF of 't2

type 't ctx =
  | Chole
  | Cbinde of string * 't * 't ctx
  | Cbindm of string * 't ctx * 't ctx

type stx =
  | Shole
  | Sbinde of string * stx
  | Sbindm of string * stx * stx

type 't expr_value =
  | Closure of string * tm * 't ctx

type 't value =
  | EVal of 't expr_value
  | MVal of 't ctx

let rec dy_to_st (c : 't ctx) =
  match c with
  | Chole -> Shole
  | Cbinde (x, _, c) -> Sbinde (x, dy_to_st c)
  | Cbindm (m, cm, c) -> Sbindm (m, dy_to_st cm, dy_to_st c)

let rec label_ctx (c : ('t * int) ctx) =
  match c with
  | Chole -> Chole
  | Cbinde (x, (_, t), c) -> Cbinde (x, t, label_ctx c)
  | Cbindm (m, cm, c) -> Cbindm (m, label_ctx cm, label_ctx c)

let rec string_of_stx (s : stx) =
  match s with
  | Shole -> "[]"
  | Sbinde (x, s) -> "\\" ^ x ^ "." ^ string_of_stx s
  | Sbindm (m, sm, s) -> "\\" ^ m ^ ":" ^ string_of_stx sm ^ "." ^ string_of_stx s

let rec plugin (cout : 't ctx) (cin : 't ctx) =
  match cout with
  | Chole -> cin
  | Cbinde (x, tx, c') -> Cbinde (x, tx, plugin c' cin)
  | Cbindm (m, cm, c') -> Cbindm (m, cm, plugin c' cin)
 
let rec level (c : 't ctx) =
  match c with
  | Chole -> 0
  | Cbinde(_, _, c') -> 1 + level c'
  | Cbindm (_, c1, c2) ->
    1 + max (level c1) (level c2)

let rec addr_x (c : 't ctx) (x : string) =
  match c with
  | Chole -> None
  | Cbinde (x', tx', c') ->
    (match addr_x c' x with
    | None -> if x = x' then (Some tx') else None
    | addr -> addr)
  | Cbindm (_, _, c') -> addr_x c' x

let rec ctx_M (c : 't ctx) (m : string) =
  match c with
  | Chole -> None
  | Cbinde (_, _, c') -> ctx_M c' m
  | Cbindm (m', cm', c') -> (
    match ctx_M c' m with
    | None -> if m = m' then Some cm' else None
    | cm -> cm)

let rec map_inject (cout : 't ctx) (cin : 't ctx) =
  match cin with
  | Chole -> Chole
  | Cbinde (x, t, c') -> Cbinde (x, t, map_inject cout c')
  | Cbindm (m, c', c'') -> Cbindm (m, plugin cout (map_inject cout c'), map_inject cout c'')
  
let inject_ctx (cout : 't ctx) (cin : 't ctx) =
  plugin cout (map_inject cout cin)

let rec delete_prefix (cout : 't ctx) (cin : 't ctx) =
  match cout, cin with
  | Chole, cin -> cin
  | Cbinde (x, t, cout'), Cbinde(x', t', cin') ->
    if x = x' && t = t' then
      delete_prefix cout' cin'
    else cin
  | Cbindm (m, cout', cout''), Cbindm (m', cin', cin'') ->
    if m = m' && cout' = cin' then
      delete_prefix cout'' cin''
    else cin
  | _, _ -> cin

let rec delete_map (cout : 't ctx) (cin : 't ctx) =
  match cin with
  | Chole -> Chole
  | Cbinde (x, t, c') ->
    Cbinde (x, t, delete_map cout c')
  | Cbindm (m, c', c'') ->
    Cbindm (m, delete_map cout (delete_prefix cout c'), delete_map cout c'')

let delete_ctx (cout : 't ctx) (cin : 't ctx) =
  delete_map cout (delete_prefix cout cin)
