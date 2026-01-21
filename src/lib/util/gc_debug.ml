(*********************************************************************************)
(*                                                                               *)
(*     Alt-Ergo: The SMT Solver For Software Verification                        *)
(*     Copyright (C) --- OCamlPro SAS                                            *)
(*                                                                               *)
(*     This software is governed by the CeCILL  license under French law and     *)
(*     abiding by the rules of distribution of free software.  You can  use,     *)
(*     modify and/ or redistribute the software under the terms of the CeCILL    *)
(*     license as circulated by CEA, CNRS and INRIA at the following URL         *)
(*     "http://www.cecill.info".                                                 *)
(*                                                                               *)
(*     As a counterpart to the access to the source code and  rights to copy,    *)
(*     modify and redistribute granted by the license, users are provided only   *)
(*     with a limited warranty  and the software's author,  the holder of the    *)
(*     economic rights,  and the successive licensors  have only  limited        *)
(*     liability.                                                                *)
(*                                                                               *)
(*     In this respect, the user's attention is drawn to the risks associated    *)
(*     with loading,  using,  modifying and/or developing or reproducing the     *)
(*     software by the user in light of its specific status of free software,    *)
(*     that may mean  that it is complicated to manipulate,  and  that  also     *)
(*     therefore means  that it is reserved for developers  and  experienced     *)
(*     professionals having in-depth computer knowledge. Users are therefore     *)
(*     encouraged to load and test the software's suitability as regards their   *)
(*     requirements in conditions enabling the security of their systems and/or  *)
(*     data to be ensured and,  more generally, to use and operate it in the     *)
(*     same conditions as regards security.                                      *)
(*                                                                               *)
(*     The fact that you are presently reading this means that you have had      *)
(*     knowledge of the CeCILL license and that you accept its terms.            *)
(*                                                                               *)
(*     ------------------------------------------------------------------------  *)
(*                                                                               *)
(*     This is a free release of Alt-Ergo under the terms of CeCILL license.     *)
(*     The latest releases of Alt-Ergo are distributed under the terms of        *)
(*     OCamlPro Non-Commercial Purpose License, version 1.                       *)
(*                                                                               *)
(*     As an exception, Alt-Ergo Club members at the Gold level can              *)
(*     use this file under the terms of the Apache Software License              *)
(*     version 2.0.                                                              *)
(*                                                                               *)
(*     ------------------------------------------------------------------------  *)
(*                                                                               *)
(*     The Alt-Ergo theorem prover                                               *)
(*                                                                               *)
(*     Sylvain Conchon, Evelyne Contejean, Francois Bobot                        *)
(*     Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout                     *)
(*                                                                               *)
(*     CNRS - INRIA - Universite Paris Sud                                       *)
(*                                                                               *)
(*     ------------------------------------------------------------------------  *)
(*                                                                               *)
(*     More details can be found in the directory licenses/                      *)
(*                                                                               *)
(*********************************************************************************)

open Options
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

let init () =
  if get_debug_gc() then
    begin
      let tmp = ref (quick_stat ()) in
      ignore
        (create_alarm
           (fun () ->
              let e = quick_stat () in
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
