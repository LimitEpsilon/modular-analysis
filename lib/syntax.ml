type tm = 
  | EVar of string
  | Lam of string * tm
  | App of tm * tm
  | LetRec of string * string * tm * tm
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
  | LetRec (f, x, e1, e2) ->
    "(fix " ^ f ^ " " ^ x ^ "=" ^ string_of_tm e1 ^ "\nin " ^ string_of_tm e2 ^ ")"
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

let rec inject (cout : 't ctx) (cin : 't ctx) =
  match cin with
  | Chole -> cout
  | Cbinde (x, tx, c') -> Cbinde (x, tx, inject cout c')
  | Cbindm (m, cm, c') -> Cbindm (m, inject cout cm, inject cout c')
 
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
    if x = x' then (Some tx') else addr_x c' x
  | Cbindm (_, _, c') -> addr_x c' x

let rec ctx_M (c : 't ctx) (m : string) =
  match c with
  | Chole -> None
  | Cbinde (_, _, c') -> ctx_M c' m
  | Cbindm (m', cm', c') ->
    if m = m' then (Some cm') else ctx_M c' m
