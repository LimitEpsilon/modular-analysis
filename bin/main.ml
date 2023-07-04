open Lambdatools
open Evaluate
open Lambda

let x = "x"
let app_my = Lam (x, App (EVar x, EVar x))
let test_tm = App (app_my, app_my)

module Mytime : (Time with type t = bool) = struct
  type t = bool
  let tick _ t _ _ = not t
  let print t =
    match t with
    | true -> print_string "T"
    | false -> print_string "F"
end

module MyAnalyzer = Analyzer(Mytime)

let init_config = (Hole, MyAnalyzer.Dom.Mem.empty, true)
let init_cache = 
  MyAnalyzer.Dom.Cache.add 
    (test_tm, init_config)
    MyAnalyzer.Dom.ResSet.empty 
    MyAnalyzer.Dom.Cache.empty

let main () =
  let analyzed = MyAnalyzer.fix init_cache in
  MyAnalyzer.Dom.print_cache analyzed

let _ = main ()
