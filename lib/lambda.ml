type tm = 
  | EVar of string
  | Lam of string * tm
  | App of tm * tm
  | Link of tm * tm
  | Empty
  | MVar of string
  | Lete of string * tm * tm
  | Letm of string * tm * tm

type ('t1, 't2) link =
  | BF of 't1
  | AF of 't2

type 't ctx =
  | Hole
  | CLam of string * 't * 't ctx
  | CLete of string * 't * 't ctx
  | CLetm of string * 't ctx * 't ctx

type 't expr_value =
  | Closure of string * tm * 't ctx

type 't value =
  | EVal of 't expr_value
  | MVal of 't ctx

let rec plugin (cout : 't ctx) (cin : 't ctx) =
  match cout with
  | Hole -> cin
  | CLam (x, tx, c') -> CLam (x, tx, plugin c' cin)
  | CLete (x, tx, c') -> CLete (x, tx, plugin c' cin)
  | CLetm (m, cm, c') -> CLetm (m, cm, plugin c' cin)
  
let rec addr_x (c : 't ctx) (x : string) =
  match c with
  | Hole -> None
  | CLam (x', tx', c')
  | CLete (x', tx', c') ->
    (match addr_x c' x with
    | None -> if x = x' then (Some tx') else None
    | addr -> addr)
  | CLetm (_, _, c') -> addr_x c' x

let rec ctx_M (c : 't ctx) (m : string) =
  match c with
  | Hole -> None
  | CLam (_, _, c')
  | CLete (_, _, c') -> ctx_M c' m
  | CLetm (m', cm', c') -> (
    match ctx_M c' m with
    | None -> if m = m' then Some cm' else None
    | cm -> cm)

let rec map_inject (cout : 't ctx) (cin : 't ctx) =
  match cin with
  | Hole -> Hole
  | CLam (x, t, c') -> CLam (x, t, map_inject cout c')
  | CLete (x, t, c') -> CLete (x, t, map_inject cout c')
  | CLetm (m, c', c'') -> CLetm (m, plugin cout (map_inject cout c'), map_inject cout c'')
  
let inject_ctx (cout : 't ctx) (cin : 't ctx) =
  plugin cout (map_inject cout cin)

let rec delete_prefix (cout : 't ctx) (cin : 't ctx) =
  match cout, cin with
  | Hole, cin -> cin
  | CLam (x, t, cout'), CLam (x', t', cin')
  | CLete (x, t, cout'), CLete(x', t', cin') ->
    if x = x' && t = t' then
      delete_prefix cout' cin'
    else cin
  | CLetm (m, cout', cout''), CLetm (m', cin', cin'') ->
    if m = m' && cout' = cin' then
      delete_prefix cout'' cin''
    else cin
  | _, _ -> cin

let rec delete_map (cout : 't ctx) (cin : 't ctx) =
  match cin with
  | Hole -> Hole
  | CLam (x, t, c') ->
    CLam (x, t, delete_map cout c')
  | CLete (x, t, c') ->
    CLete (x, t, delete_map cout c')
  | CLetm (m, c', c'') ->
    CLetm (m, delete_map cout (delete_prefix cout c'), delete_map cout c'')

let delete_ctx (cout : 't ctx) (cin : 't ctx) =
  delete_map cout (delete_prefix cout cin)
