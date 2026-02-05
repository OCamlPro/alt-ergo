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

let remove_trailing_whitespaces line =
  let len = String.length line in
  let new_len = ref len in
  let loop = ref (!new_len > 0) in
  while !loop do
    let c = line.[!new_len - 1] in
    if c = ' ' || c = '\t' || c = '\r' then
      begin
        decr new_len;
        loop := !new_len > 0
      end
    else loop := false
  done;
  if !new_len <> len then Some (String.sub line 0 !new_len)
  else None

let check_buffer file cin =
  let spacesRemoved = ref false in
  let longLines = ref false in
  let lines = Queue.create () in
  let cpt = ref 0 in
  try
    while true do
      incr cpt;
      let line = input_line cin in
      let line =
        match remove_trailing_whitespaces line with
        | None       -> Queue.push line  lines; line
        | Some line2 -> Queue.push line2 lines; spacesRemoved := true; line2
      in
      if String.length line > 80 then begin
        Format.eprintf "File %s: line %d too long@." file !cpt;
        longLines := true;
      end
    done;
    assert false
  with End_of_file -> lines, !spacesRemoved, !longLines

let update_file file lines =
  let cout =
    try open_out file
    with e ->
      Format.eprintf "Error while opening (out) file: %s@.%s@."
        file (Printexc.to_string e);
      exit 2
  in
  Queue.iter (fun line ->
      Stdlib.output_string cout line;
      Stdlib.output_string cout "\n"
    )lines;
  Stdlib.flush cout;
  close_out cout


let check_file file =
  let cin =
    try open_in file
    with e ->
      Format.eprintf "Error while opening (in) file: %s@.%s@."
        file (Printexc.to_string e);
      exit 2
  in
  let lines, spacesRemoved, longLines = check_buffer file cin in
  close_in cin;
  if spacesRemoved then begin
    update_file file lines;
    exit 10
  end;
  if longLines then exit 11


let () =
  match Array.length Sys.argv with
  | 0 | 1 ->
    Format.eprintf "%s: Too few arguments!@." Sys.argv.(0); exit 3
  | 2 ->
    check_file Sys.argv.(1)

  | _ ->
    Format.eprintf "%s: Too many arguments!@." Sys.argv.(0); exit 4
