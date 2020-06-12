
include Format

let pp_open_stag = pp_open_tag
let open_stag = open_tag
let pp_close_stag = pp_close_tag
let close_stag = close_tag

type formatter_stag_functions = formatter_tag_functions

let pp_get_formatter_stag_functions = pp_get_formatter_tag_functions
let get_formatter_stag_functions = get_formatter_tag_functions
let pp_set_formatter_stag_functions = pp_set_formatter_tag_functions
let set_formatter_stag_functions = set_formatter_tag_functions

let get_stag s = s

let update_stag_functions funs start_stag stop_stag =
  let open Format in
  { funs with
    mark_open_tag = start_stag;
    mark_close_tag = stop_stag }

