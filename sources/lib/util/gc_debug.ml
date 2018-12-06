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

open Options
open Format
open Gc

(*
 major_collections; (* num of completed major collection cycles *)
 minor_collections; (* num of minor collections *)
 stack_size; (* current size of the stack, in word *)

 heap_words; (* tot size of the major heap *)
 top_heap_words; (* Max size reached by major heap *)

 minor_words; (* num of alloc words in minor heap since beginning *)
 major_words; (* num of alloc words in major heap, since beginning *)
*)

let () =
  if debug_gc() then
    begin
      let tmp = ref (quick_stat ()) in
      ignore
        (create_alarm
           (fun () ->
              let e = quick_stat () in
              let d = !tmp in
              fprintf fmt "[GC infos]======================================@.";
              fprintf fmt "[major collections] %d th@." e.major_collections;
              fprintf fmt "[minor collections] %d th@." e.minor_collections;
              fprintf fmt "[stack used] %d words@." e.stack_size;
              fprintf fmt "[size of major heap] %d words@." e.heap_words;
              fprintf fmt "[max size major heap] %d words@." e.top_heap_words;
              fprintf fmt "[major words diff] %0f Kwords@."
                ((e.major_words -. d.major_words) /. 1000.);
              fprintf fmt "[minor words diff] %0f Kwords@."
                ((e.minor_words -. d.minor_words) /. 1000.);
              tmp := e
           )
        )
    end
