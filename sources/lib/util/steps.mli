type incr_kind =
    Matching (* Matching step increment *)
  | Omega (* Step of Arith on Real and Int *)
  | Fourier (* FourierMotzkin step increment *)
  | Uf (* UF step increment *)
  | Builtin (* Inequalities increment *)
  | Ac (* AC step reasoning *)
  | Naive of int (* Naive way of counting steps is to increment the counter for
                  * each term assumed in the theories environment *)
(** Define the type of increment *)

val incr  : incr_kind -> unit
(** Increment the number of steps depending of the incr_kind
    and check if the number of steps is inbound by the -steps-bound option.
    Exit if the number of steps is reached *)

val reset_steps : unit -> unit
(** Reset the global steps counter *)

val get_steps : unit -> int
(** Return the number of steps *)
