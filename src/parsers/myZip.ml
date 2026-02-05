(******************************************************************************)
(*                                                                            *)
(*  Alt-Ergo: The SMT Solver For Software Verification                        *)
(*  Copyright (C) --- OCamlPro SAS                                            *)
(*                                                                            *)
(*  This software is governed by the CeCILL  license under French law and     *)
(*  abiding by the rules of distribution of free software.  You can  use,     *)
(*  modify and/ or redistribute the software under the terms of the CeCILL    *)
(*  license as circulated by CEA, CNRS and INRIA at the following URL         *)
(*  "http://www.cecill.info".                                                 *)
(*                                                                            *)
(*  As a counterpart to the access to the source code and  rights to copy,    *)
(*  modify and redistribute granted by the license, users are provided only   *)
(*  with a limited warranty  and the software's author,  the holder of the    *)
(*  economic rights,  and the successive licensors  have only  limited        *)
(*  liability.                                                                *)
(*                                                                            *)
(*  In this respect, the user's attention is drawn to the risks associated    *)
(*  with loading,  using,  modifying and/or developing or reproducing the     *)
(*  software by the user in light of its specific status of free software,    *)
(*  that may mean  that it is complicated to manipulate,  and  that  also     *)
(*  therefore means  that it is reserved for developers  and  experienced     *)
(*  professionals having in-depth computer knowledge. Users are therefore     *)
(*  encouraged to load and test the software's suitability as regards their   *)
(*  requirements in conditions enabling the security of their systems and/or  *)
(*  data to be ensured and,  more generally, to use and operate it in the     *)
(*  same conditions as regards security.                                      *)
(*                                                                            *)
(*  The fact that you are presently reading this means that you have had      *)
(*  knowledge of the CeCILL license and that you accept its terms.            *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*  This is a free release of Alt-Ergo under the terms of CeCILL license.     *)
(*  The latest releases of Alt-Ergo are distributed under the terms of        *)
(*  OCamlPro Non-Commercial Purpose License, version 1.                       *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*  The Alt-Ergo theorem prover                                               *)
(*                                                                            *)
(*  Sylvain Conchon, Evelyne Contejean, Francois Bobot                        *)
(*  Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout                     *)
(*                                                                            *)
(*  CNRS - INRIA - Universite Paris Sud                                       *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*  More details can be found in the directory licenses/                      *)
(*                                                                            *)
(******************************************************************************)

(** A wrapper of the Zip module of CamlZip: we use Zip except when we want to
    generate the.js file for try-Alt-Ergo **)

module ZipWrapper = struct
  include Zip
  let filename e = e.Zip.filename
  let is_directory e = e.Zip.is_directory
end

include ZipWrapper

(* !! This commented code is used when compiling to javascript !!
   module DummyZip = struct
   type entry = unit
   type in_file = unit

   let s = "Zip module not available for your setting or has been disabled !"

   let open_in  _  =  failwith s
   let close_in _ = failwith s
   let entries  _  =  failwith s
   let read_entry  _ _  =  failwith s
   let filename  _  =  failwith s
   let is_directory  _  =  failwith s
   end

   include DummyZip
*)
