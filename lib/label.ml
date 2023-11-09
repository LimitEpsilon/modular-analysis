open Syntax

type lbl = int

type lblled_tm =
  | LEVar of string
  | LLam of string * lbl
  | LApp of lbl * lbl
  | LLetRec of string * string * lbl * lbl
  | LLink of lbl * lbl
  | LEmpty
  | LMVar of string
  | LLete of string * lbl * lbl
  | LLetm of string * lbl * lbl

type 't lblled_expr_value = LClosure of string * lbl * 't ctx
type 't lblled_value = LEVal of 't lblled_expr_value | LMVal of 't ctx

let label_tbl : (lbl, lblled_tm) Hashtbl.t = Hashtbl.create 10
let _label : lbl ref = ref 0

let new_label () =
  let label = !_label in
  incr _label;
  label

let rec label_tm (e : tm) =
  let l = new_label () in
  let lblled =
    match e with
    | EVar x -> LEVar x
    | Lam (x, e) ->
      let e = label_tm e in
      LLam (x, e)
    | App (e1, e2) ->
      let e1 = label_tm e1 in
      let e2 = label_tm e2 in
      LApp (e1, e2)
    | LetRec (f, x, e1, e2) ->
      let e1 = label_tm e1 in
      let e2 = label_tm e2 in
      LLetRec (f, x, e1, e2)
    | Link (m, e) ->
      let m = label_tm m in
      let e = label_tm e in
      LLink (m, e)
    | Empty -> LEmpty
    | MVar m -> LMVar m
    | Lete (x, e, m) ->
      let e = label_tm e in
      let m = label_tm m in
      LLete (x, e, m)
    | Letm (m, m1, m2) ->
      let m1 = label_tm m1 in
      let m2 = label_tm m2 in
      LLetm (m, m1, m2)
  in
  Hashtbl.add label_tbl l lblled;
  l

let string_of_lexp = function
  | LEVar x -> x
  | LLam (x, l) -> "\\" ^ x ^ "." ^ string_of_int l
  | LApp (l1, l2) -> string_of_int l1 ^ " " ^ string_of_int l2
  | LLetRec (f, x, l1, l2) ->
    "let rec " ^ f ^ " " ^ x ^ " = " ^ string_of_int l1 ^ " in "
    ^ string_of_int l2
  | LLink (l1, l2) -> "include " ^ string_of_int l1 ^ " in " ^ string_of_int l2
  | LEmpty -> "empty"
  | LMVar m -> m
  | LLete (x, e, m) ->
    "let " ^ x ^ " = " ^ string_of_int e ^ " in " ^ string_of_int m
  | LLetm (m, m1, m2) ->
    "let " ^ m ^ " = " ^ string_of_int m1 ^ " in " ^ string_of_int m2

let rec label_tbl_string n acc =
  if n <= 0 then
    match Hashtbl.find_opt label_tbl n with
    | Some e -> label_tbl_string 1 (string_of_int n ^ " : " ^ string_of_lexp e)
    | None -> ""
  else
    match Hashtbl.find_opt label_tbl n with
    | Some e ->
      label_tbl_string (n + 1)
        (acc ^ "\n" ^ string_of_int n ^ " : " ^ string_of_lexp e)
    | None -> acc

let print_labels () = print_endline (label_tbl_string 0 "")
