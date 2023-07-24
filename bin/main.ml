open Modular
open Analyze
open Syntax

type time = string * stx * stx * int
let precision = ref 20

module Mytime : (Time with type t = time) = struct
  type t = time
  let tick c (_, _, _, t) x v = 
    match v with
    | Closure (_, _, c') -> (x, dy_to_st c, dy_to_st c', (t + 1) mod !precision)
  let string_of_time t =
    match t with
    | (x, s1, s2, _) -> "(" ^ x ^ ", " ^ string_of_stx s1 ^ ", " ^ string_of_stx s2 ^ ")"
end

module MyAnalyzer = Analyzer(Mytime)

let init_config = (Chole, ("$", Shole, Shole, 0))

let main () =
  let src = ref "" in
  let _ =
    Arg.parse
      [("-precision",
          Arg.Int
            (fun n -> precision := n), "Increase accuracy of analysis");]
      (fun x -> src := x)
      ("Usage: " ^ Filename.basename Sys.argv.(0) ^ " -precision [precision] [file]")
  in
  let () = if !precision < 1 then failwith "Precision must be above 0!" in
  let lexbuf =
    Lexing.from_channel (if !src = "" then stdin else open_in !src)
  in
  let pgm = Parser.program Lexer.start lexbuf in
  let init_cache =
    MyAnalyzer.Dom.Cache.add 
      (pgm, init_config)
      MyAnalyzer.Dom.ResSet.empty
      MyAnalyzer.Dom.Cache.empty in
  let init_mem = MyAnalyzer.Dom.Mem.empty in
  let analyzed, _ = MyAnalyzer.fix 0 init_cache init_mem in
  let final = MyAnalyzer.Dom.Cache.find (pgm, init_config) analyzed in
  MyAnalyzer.Dom.print_resset final;
  print_newline ()

let _ = main ()
