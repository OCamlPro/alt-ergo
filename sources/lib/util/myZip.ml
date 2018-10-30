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
