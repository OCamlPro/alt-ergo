(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

(** TODO: use the newly available Sys.backend_type to simplify things ? *)

module Default_Unix = struct

  open Unix

  let cur_time () = (times()).tms_utime

  let set_timeout ~is_gui timelimit =
    if Pervasives.(<>) timelimit 0. then
      let itimer =
        if is_gui then Unix.ITIMER_REAL (* troubles with VIRTUAL *)
        else Unix.ITIMER_VIRTUAL
      in
      ignore (Unix.setitimer itimer
                { Unix.it_value = timelimit; Unix.it_interval = 0. })

  let unset_timeout ~is_gui =
    let itimer =
      if is_gui then Unix.ITIMER_REAL (* troubles with VIRTUAL *)
      else Unix.ITIMER_VIRTUAL
    in
    ignore (Unix.setitimer itimer
              { Unix.it_value = 0.; Unix.it_interval = 0. })

end

include Default_Unix

(* !! This commented code is used when compiling to javascript !!
   module JavaScript_Unix = struct

   let cur_time () =
    let today = jsnew Js.date_now () in
    let t = Js.to_float (today##getTime()) in
    t /. 1000.

   let set_timeout _ = ()

   let unset_timeout () = ()

   end

   include JavaScript_Unix
*)
