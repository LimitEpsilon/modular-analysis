type 'e t

val empty : 'e t
val add : 'e -> 'e t -> 'e t
val singleton : 'e -> 'e t
val remove : 'e -> 'e t -> 'e t
val union : 'e t -> 'e t -> 'e t
val inter : 'e t -> 'e t -> 'e t
val disjoint : 'e t -> 'e t -> bool
val diff : 'e t -> 'e t -> 'e t
val cardinal : 'e t -> int
val elements : 'e t -> 'e list
val min_elt : 'e t -> 'e
val min_elt_opt : 'e t -> 'e option
val max_elt : 'e t -> 'e
val max_elt_opt : 'e t -> 'e option
val choose : 'e t -> 'e
val choose_opt : 'e t -> 'e option
val find : 'e -> 'e t -> 'e
val find_opt : 'e -> 'e t -> 'e option
val find_first : ('e -> bool) -> 'e t -> 'e
val find_first_opt : ('e -> bool) -> 'e t -> 'e option
val find_last : ('e -> bool) -> 'e t -> 'e
val find_last_opt : ('e -> bool) -> 'e t -> 'e option
val iter : ('e -> unit) -> 'e t -> unit
val fold : ('e -> 'a -> 'a) -> 'e t -> 'a -> 'a
val map : ('e -> 'e) -> 'e t -> 'e t
val filter : ('e -> bool) -> 'e t -> 'e t
val filter_map : ('e -> 'e option) -> 'e t -> 'e t
val partition : ('e -> bool) -> 'e t -> 'e t * 'e t
val split : 'e -> 'e t -> 'e t * bool * 'e t
val is_empty : 'e t -> bool
val mem : 'e -> 'e t -> bool
val equal : 'e t -> 'e t -> bool
val compare : 'e t -> 'e t -> int
val subset : 'e t -> 'e t -> bool
val for_all : ('e -> bool) -> 'e t -> bool
val exists : ('e -> bool) -> 'e t -> bool
val to_list : 'e t -> 'e list
val of_list : 'e list -> 'e t
val to_seq_from : 'e -> 'e t -> 'e Seq.t
val to_seq : 'e t -> 'e Seq.t
val to_rev_seq : 'e t -> 'e Seq.t
val add_seq : 'e Seq.t -> 'e t -> 'e t
val of_seq : 'e Seq.t -> 'e t
