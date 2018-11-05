module Make (Th : Theory.S) : sig

  type t

  val empty : unit -> t

  val is_true : t -> Formula.t -> (Explanation.t Lazy.t * int) option

  val assume : bool -> t -> (Formula.gformula * Explanation.t) list -> t

  val decide : t -> Formula.t -> int -> t

  (* forget decisions one by one *)
  val forget_decision : t -> Formula.t -> int -> t

  val reset_decisions : t -> t
  (*val solve : t -> t*)

  val get_decisions : t -> (int * Formula.t) list

end
