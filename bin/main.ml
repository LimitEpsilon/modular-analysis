open Lambdatools
open Evaluate
open Lambda

(*let x = "x"
let app_my = Lam (x, App (EVar x, EVar x))
let test_tm = App (app_my, app_my)*)

module Mytime : (Time with type t = int) = struct
  type t = int
  let tick _ t _ _ = t + 1
  let print t = print_int t (*
    match t with
    | true -> print_string "T"
    | false -> print_string "F"*)
end

module MyAnalyzer = Analyzer(Mytime)

let init_config = (Hole, MyAnalyzer.Dom.Mem.empty, 0)
(*let init_cache = 
  MyAnalyzer.Dom.Cache.add 
    (test_tm, init_config)
    MyAnalyzer.Dom.ResSet.empty 
    MyAnalyzer.Dom.Cache.empty*)

let main () =
  let src = ref "" in
  let _ =
    Arg.parse
      []
      (fun x -> src := x)
      ("Usage: " ^ Filename.basename Sys.argv.(0) ^ " [file]")
  in
  let lexbuf =
    Lexing.from_channel (if !src = "" then stdin else open_in !src)
  in
  let pgm = Parser.program Lexer.start lexbuf in
  let init_cache = 
    MyAnalyzer.Dom.Cache.add 
      (pgm, init_config)
      MyAnalyzer.Dom.ResSet.empty
      MyAnalyzer.Dom.Cache.empty in
  let analyzed = MyAnalyzer.fix init_cache in
  MyAnalyzer.Dom.print_cache analyzed

let _ = main ()
