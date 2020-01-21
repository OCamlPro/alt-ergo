type incr_kind = Matching | Omega | Fourier | Uf | Builtin | Ac | Naive of int

val incr  : incr_kind -> unit
(** Increment the number of steps depending of the incr_kind
    and check if the number of steps is inbound by the -steps-bound option.
    Exit if the number of steps is reached *)

val reset_steps : unit -> unit
(** Reset the global steps counter *)

val get_steps : unit -> int
(** Return the number of steps *)