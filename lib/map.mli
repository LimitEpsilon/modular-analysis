(** Polymorphic Maps *)

(* The type 'k must be a type that can be compared well by the polymorphic compare function *)

type ('k, 'a) t

val empty : ('k, 'a) t
val add : 'k -> 'a -> ('k, 'a) t -> ('k, 'a) t
val add_to_list : 'k -> 'a -> ('k, 'a list) t -> ('k, 'a list) t
val update : 'k -> ('a option -> 'a option) -> ('k, 'a) t -> ('k, 'a) t
val singleton : 'k -> 'a -> ('k, 'a) t
val remove : 'k -> ('k, 'a) t -> ('k, 'a) t

val merge :
  ('k -> 'a option -> 'b option -> 'c option) ->
  ('k, 'a) t ->
  ('k, 'b) t ->
  ('k, 'c) t

val union :
  ('k -> 'a -> 'a -> 'a option) -> ('k, 'a) t -> ('k, 'a) t -> ('k, 'a) t

val cardinal : ('k, 'a) t -> int
val bindings : ('k, 'a) t -> ('k * 'a) list
val min_binding : ('k, 'a) t -> 'k * 'a
val min_binding_opt : ('k, 'a) t -> ('k * 'a) option
val max_binding : ('k, 'a) t -> 'k * 'a
val max_binding_opt : ('k, 'a) t -> ('k * 'a) option
val choose : ('k, 'a) t -> 'k * 'a
val choose_opt : ('k, 'a) t -> ('k * 'a) option
val find : 'k -> ('k, 'a) t -> 'a
val find_opt : 'k -> ('k, 'a) t -> 'a option
val find_first : ('k -> bool) -> ('k, 'a) t -> 'k * 'a
val find_first_opt : ('k -> bool) -> ('k, 'a) t -> ('k * 'a) option
val find_last : ('k -> bool) -> ('k, 'a) t -> 'k * 'a
val find_last_opt : ('k -> bool) -> ('k, 'a) t -> ('k * 'a) option
val iter : ('k -> 'a -> unit) -> ('k, 'a) t -> unit
val fold : ('k -> 'a -> 'b -> 'b) -> ('k, 'a) t -> 'b -> 'b
val map : ('a -> 'b) -> ('k, 'a) t -> ('k, 'b) t
val mapi : ('k -> 'a -> 'b) -> ('k, 'a) t -> ('k, 'b) t
val filter : ('k -> 'a -> bool) -> ('k, 'a) t -> ('k, 'a) t
val filter_map : ('k -> 'a -> 'b option) -> ('k, 'a) t -> ('k, 'b) t
val partition : ('k -> 'a -> bool) -> ('k, 'a) t -> ('k, 'a) t * ('k, 'a) t
val split : 'k -> ('k, 'a) t -> ('k, 'a) t * 'a option * ('k, 'a) t
val is_empty : ('k, 'a) t -> bool
val mem : 'k -> ('k, 'a) t -> bool
val equal : ('a -> 'a -> bool) -> ('k, 'a) t -> ('k, 'a) t -> bool
val compare : ('a -> 'a -> int) -> ('k, 'a) t -> ('k, 'a) t -> int
val for_all : ('k -> 'a -> bool) -> ('k, 'a) t -> bool
val exists : ('k -> 'a -> bool) -> ('k, 'a) t -> bool
val to_list : ('k, 'a) t -> ('k * 'a) list
val of_list : ('k * 'a) list -> ('k, 'a) t
val to_seq : ('k, 'a) t -> ('k * 'a) Seq.t
val to_rev_seq : ('k, 'a) t -> ('k * 'a) Seq.t
val to_seq_from : 'k -> ('k, 'a) t -> ('k * 'a) Seq.t
val add_seq : ('k * 'a) Seq.t -> ('k, 'a) t -> ('k, 'a) t
val of_seq : ('k * 'a) Seq.t -> ('k, 'a) t
