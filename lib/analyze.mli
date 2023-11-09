open Syntax

val print_iter : bool ref

type time_without_label = string * stx list
type time = time_without_label * int

type 't valSet = 't expr_value Set.t
type 't memory = ('t, 't valSet) Map.t
type 't state = 't ctx * 't
type 't config = tm * 't state
type 't result = 't value * 't
type 't resSet = 't result Set.t
type 't cache = ('t config, 't resSet) Map.t
type 't tick = 't ctx -> 't -> string -> 't expr_value -> 't

val string_of_ctx : ('time -> string) -> 'time ctx -> string
val string_of_ev : ('time -> string) -> 'time expr_value -> string
val string_of_val : ('time -> string) -> 'time value -> string
val print_valset : ('time -> string) -> 'time valSet -> unit
val print_mem : ('time -> string) -> 'time memory -> unit
val print_state : ('time -> string) -> 'time state -> unit
val print_result : ('time -> string) -> 'time result -> unit
val print_resset : ('time -> string) -> 'time resSet -> unit
val print_cache : ('time -> string) -> 'time cache -> unit

val add_worklist : time config -> unit
val eval_cache :
  tm ->
  time state ->
  time cache ->
  time memory ->
  time tick ->
  time cache * time memory

val fix :
  int -> time cache -> time memory -> time tick -> time cache * time memory
