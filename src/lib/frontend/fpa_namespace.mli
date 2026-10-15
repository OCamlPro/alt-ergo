(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) --- OCamlPro SAS                                     *)
(*                                                                        *)
(*     This file is distributed under the terms of OCamlPro               *)
(*     Non-Commercial Purpose License, version 1.                         *)
(*                                                                        *)
(*     As an exception, Alt-Ergo Club members at the Gold level can       *)
(*     use this file under the terms of the Apache Software License       *)
(*     version 2.0.                                                       *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

(** Loading of the SMT-LIB FPA prelude.

    The statements of the prelude [src/preludes/why3-fpa/smt-lib-fpa.ae] are
    renamed before type-checking: the declared and defined symbols are prefixed
    with [ae.fp.] ([add] becomes [ae.fp.add]), [pow2] is the builtin [int.pow2]
    and [round] is the builtin [ae.float].

    Only [logic] declarations, [function] and [predicate] definitions, and
    axioms are supported. *)

type t
(** The state of the renaming of the prelude. *)

val create : unit -> t
(** Creates a new renaming state, to be used for a single loading of the
    prelude. *)

val rewrite : t -> Dolmen.Std.Statement.t -> Dolmen.Std.Statement.t
(** [rewrite t stmt] renames the symbols of the parsed statement [stmt] of the
    prelude.

    @raise Failure if the statement is not supported. *)
