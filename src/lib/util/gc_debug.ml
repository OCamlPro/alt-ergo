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
(*     The Alt-Ergo theorem prover                                        *)
(*                                                                        *)
(*     Sylvain Conchon, Evelyne Contejean, Francois Bobot                 *)
(*     Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout              *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

(*
 major_collections; (* num of completed major collection cycles *)
 minor_collections; (* num of minor collections *)
 stack_size; (* current size of the stack, in word *)

 heap_words; (* tot size of the major heap *)
 top_heap_words; (* Max size reached by major heap *)

 minor_words; (* num of alloc words in minor heap since beginning *)
 major_words; (* num of alloc words in major heap, since beginning *)
*)

let src = Logs.Src.create ~doc:"Gc_debug" __MODULE__
module Log = (val Logs.src_log src : Logs.LOG)

let init () =
  if Options.get_debug_gc() then
    begin
      let tmp = ref (Gc.quick_stat ()) in
      ignore
        (Gc.create_alarm
           (fun () ->
              let e = Gc.quick_stat () in
              let d = !tmp in

              Printer.print_dbg
                ~module_name:"Gc_debug"
                "@[<v 0>[major collections] %d th@,\
                 [minor collections] %d th@,\
                 [stack used] %d words@,\
                 [size of major heap] %d words@,\
                 [max size major heap] %d words@,\
                 [major words diff] %0f Kwords@,\
                 [minor words diff] %0f Kwords@]"
                e.major_collections
                e.minor_collections
                e.stack_size
                e.heap_words
                e.top_heap_words
                ((e.major_words -. d.major_words) /. 1000.)
                ((e.minor_words -. d.minor_words) /. 1000.);
              tmp := e
           )
        )
    end
