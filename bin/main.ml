open Modular
open Analyze
open Syntax

type time_without_label = string * tm
type time = time_without_label * int

let precision = ref 20

let tick _ (_, t) x v =
  match v with
  | Closure (xx, ee, _) ->
    let without_label = (x, Lam (xx, ee)) in
    (without_label, (t + 1) mod !precision)

let string_of_time t =
  match t with
  | (x, e), _ ->
    "(" ^ x ^ ", "
    ^ string_of_tm e
    ^ ")"

let init_time = ("$", EVar "$")
let init_config = (Chole, (init_time, 0))

let main () =
  let src = ref "" in
  let _ =
    Arg.parse
      [
        ( "-precision",
          Arg.Int (fun n -> precision := n),
          "Increase accuracy of analysis" );
        ( "-print_iter",
          Arg.Unit (fun () -> print_iter := true),
          "Print number of iterations" );
      ]
      (fun x -> src := x)
      ("Usage: "
      ^ Filename.basename Sys.argv.(0)
      ^ " [-precision precision] [-print_iter] <file>")
  in
  let () = if !precision < 1 then failwith "Precision must be above 0!" in
  let lexbuf =
    Lexing.from_channel (if !src = "" then stdin else open_in !src)
  in
  let pgm = Parser.program Lexer.start lexbuf in
  let init_cache : time cache =
    Map.add (pgm, init_config) Set.empty Map.empty
  in
  let init_mem : time memory = Map.empty in
  let analyzed, _ = fix 0 init_cache init_mem tick in
  let final = Map.find (pgm, init_config) analyzed in
  print_resset string_of_time final;
  print_newline ()

let _ = main ()
