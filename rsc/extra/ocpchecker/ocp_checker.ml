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
