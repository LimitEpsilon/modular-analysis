open Modular
open Analyze
open Syntax

type time = string * stx * stx * int

let precision = ref 20

let tick c (_, _, _, t) x v =
  match v with
  | Closure (_, _, c') -> (x, dy_to_st c, dy_to_st c', (t + 1) mod !precision)

let string_of_time t =
  match t with
  | x, s1, s2, _ ->
    "(" ^ x ^ ", " ^ string_of_stx s1 ^ ", " ^ string_of_stx s2 ^ ")"

let init_config = (Chole, ("$", Shole, Shole, 0))

let main () =
  let src = ref "" in
  let _ =
    Arg.parse
      [
        ( "-precision",
          Arg.Int (fun n -> precision := n),
          "Increase accuracy of analysis" );
      ]
      (fun x -> src := x)
      ("Usage: "
      ^ Filename.basename Sys.argv.(0)
      ^ " -precision [precision] [file]")
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
