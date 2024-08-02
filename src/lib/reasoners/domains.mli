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

module Make
    (NF : Domains_intf.NormalForm)
    (D : Domains_intf.Domain
     with type var = NF.Composite.t
      and type atom = NF.Atom.t
      and type constant = NF.constant)
    (W : Domains_intf.OrderedType)
  : Domains_intf.S
    with module NF := NF
     and type domain := D.t
     and type watch := W.t
