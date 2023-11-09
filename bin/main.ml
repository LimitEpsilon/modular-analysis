open Modular
open Analyze
open Syntax

let precision = ref 20
let k = ref 0

(* let rec last (c : time ctx) =
   match c with
   | Chole -> []
   | Cbinde (_, ((_, l), _), _) -> l
   | Cbindm (_, _, c) -> last c *)

let rec lblled_last (c : Lbl_analyze.time ctx) =
  match c with
  | Chole -> []
  | Cbinde (_, ((_, l), _), _) -> l
  | Cbindm (_, _, c) -> lblled_last c

let rec top k l =
  match l with
  | [] -> []
  | hd :: tl -> if k <= 0 then [] else hd :: top (k - 1) tl

(* let tick c (_, t) x _ =
   let callsite = dy_to_st c in
   let last_callsites = last c in
   let wo_label = (x, top !k (callsite :: last_callsites)) in
   (wo_label, (t + 1) mod !precision) *)

let lblled_tick l c x lx =
  let callsite = l in
  let last_callsites = lblled_last c in
  let wo_label = ((x, lx), top !k (callsite :: last_callsites)) in
  (wo_label, 0)

let string_of_list f l =
  let for_each_n (s, first) n =
    if first then (s ^ f n, false) else (s ^ ";" ^ f n, first)
  in
  let s, _ = List.fold_left for_each_n ("[", true) l in
  s ^ "]"

let string_of_lblled_time = function
  | ((_, _), l), _ -> string_of_list string_of_int l

(* let string_of_time = function _, n -> string_of_int n
   let init_time = (("$", []), 0) *)
let init_state = Chole

let main () =
  let src = ref "" in
  let _ =
    Arg.parse
      [
        ( "-precision",
          Arg.Int (fun n -> precision := n),
          "Increase accuracy of analysis" );
        ("-k", Arg.Int (fun n -> k := n), "k-CFA");
        ( "-timeout",
          Arg.Int (fun n -> Lbl_analyze.timeout := n),
          "Set maximum number of iterations" );
        ( "-print_iter",
          Arg.Unit
            (fun () ->
              print_iter := true;
              Lbl_analyze.print_iter := true),
          "Print number of iterations" );
      ]
      (fun x -> src := x)
      ("Usage: "
      ^ Filename.basename Sys.argv.(0)
      ^ " [-k k-CFA level] [-timeout max_iters] [-precision precision] \
         [-print_iter] <file>")
  in
  let () = if !precision < 1 then failwith "Precision must be above 0!" in
  let lexbuf =
    Lexing.from_channel (if !src = "" then stdin else open_in !src)
  in
  let pgm = Parser.program Lexer.start lexbuf in
  let lblled_pgm = Label.label_tm pgm in
  Label.print_labels ();
  let open Lbl_analyze in
  add_worklist (lblled_pgm, init_state);
  let init_cache : time cache =
    Map.add (lblled_pgm, init_state) Set.empty Map.empty
  in
  let init_mem : time memory = Map.empty in
  let analyzed, _ = fix 0 init_cache init_mem lblled_tick in
  let final = Map.find (lblled_pgm, init_state) analyzed in
  print_resset string_of_lblled_time final;
  print_newline ()

let _ = main ()
