
module MenhirBasics = struct
  
  exception Error = Parsing.Parse_error
  
  type token = 
    | XOR
    | WITH
    | VOID
    | UNIT
    | TYPE
    | TRUE
    | TIMES
    | THEORY
    | THEN
    | STRING of (
# 42 "src/parsers/why_parser.mly"
       (string)
# 20 "src/parsers/why_parser.ml"
  )
    | SLASH
    | SHARP
    | RIGHTSQ
    | RIGHTPAR
    | RIGHTBR
    | RIGHTARROW
    | REWRITING
    | REAL
    | QUOTE
    | QM_ID of (
# 39 "src/parsers/why_parser.mly"
       (string)
# 34 "src/parsers/why_parser.ml"
  )
    | QM
    | PV
    | PROP
    | PRED
    | POWDOT
    | POW
    | PLUS
    | PERCENT
    | OR
    | OF
    | NUM of (
# 41 "src/parsers/why_parser.mly"
       (Num.num)
# 49 "src/parsers/why_parser.ml"
  )
    | NOTEQ
    | NOT
    | MINUS
    | MATCH
    | MAPS_TO
    | LT
    | LRARROW
    | LOGIC
    | LET
    | LEFTSQ
    | LEFTPAR
    | LEFTBR
    | LEFTARROW
    | LE
    | INTEGER of (
# 40 "src/parsers/why_parser.mly"
       (string)
# 68 "src/parsers/why_parser.ml"
  )
    | INT
    | IN
    | IF
    | ID of (
# 38 "src/parsers/why_parser.mly"
       (string)
# 76 "src/parsers/why_parser.ml"
  )
    | HAT
    | GT
    | GOAL
    | GE
    | FUNC
    | FORALL
    | FALSE
    | EXTENDS
    | EXISTS
    | EQUAL
    | EOF
    | END
    | ELSE
    | DOT
    | DISTINCT
    | CUT
    | COMMA
    | COLON
    | CHECK
    | CASESPLIT
    | BOOL
    | BITV
    | BAR
    | AXIOM
    | AT
    | AND
    | AC
  
end

include MenhirBasics

let _eRR =
  MenhirBasics.Error

type _menhir_env = {
  _menhir_lexer: Lexing.lexbuf -> token;
  _menhir_lexbuf: Lexing.lexbuf;
  _menhir_token: token;
  mutable _menhir_error: bool
}

and _menhir_state = 
  | MenhirState352
  | MenhirState348
  | MenhirState346
  | MenhirState341
  | MenhirState339
  | MenhirState336
  | MenhirState335
  | MenhirState334
  | MenhirState331
  | MenhirState329
  | MenhirState327
  | MenhirState325
  | MenhirState324
  | MenhirState322
  | MenhirState318
  | MenhirState316
  | MenhirState314
  | MenhirState310
  | MenhirState308
  | MenhirState304
  | MenhirState303
  | MenhirState300
  | MenhirState298
  | MenhirState296
  | MenhirState294
  | MenhirState291
  | MenhirState289
  | MenhirState287
  | MenhirState283
  | MenhirState281
  | MenhirState275
  | MenhirState273
  | MenhirState269
  | MenhirState266
  | MenhirState262
  | MenhirState259
  | MenhirState257
  | MenhirState256
  | MenhirState253
  | MenhirState251
  | MenhirState242
  | MenhirState239
  | MenhirState237
  | MenhirState234
  | MenhirState232
  | MenhirState228
  | MenhirState225
  | MenhirState224
  | MenhirState214
  | MenhirState211
  | MenhirState208
  | MenhirState204
  | MenhirState201
  | MenhirState197
  | MenhirState192
  | MenhirState186
  | MenhirState185
  | MenhirState183
  | MenhirState180
  | MenhirState175
  | MenhirState172
  | MenhirState170
  | MenhirState168
  | MenhirState166
  | MenhirState164
  | MenhirState162
  | MenhirState160
  | MenhirState158
  | MenhirState156
  | MenhirState154
  | MenhirState152
  | MenhirState150
  | MenhirState148
  | MenhirState146
  | MenhirState144
  | MenhirState142
  | MenhirState140
  | MenhirState138
  | MenhirState133
  | MenhirState124
  | MenhirState122
  | MenhirState120
  | MenhirState118
  | MenhirState115
  | MenhirState113
  | MenhirState112
  | MenhirState111
  | MenhirState109
  | MenhirState108
  | MenhirState107
  | MenhirState106
  | MenhirState105
  | MenhirState104
  | MenhirState102
  | MenhirState101
  | MenhirState99
  | MenhirState96
  | MenhirState92
  | MenhirState91
  | MenhirState90
  | MenhirState86
  | MenhirState82
  | MenhirState81
  | MenhirState75
  | MenhirState73
  | MenhirState72
  | MenhirState71
  | MenhirState70
  | MenhirState68
  | MenhirState64
  | MenhirState62
  | MenhirState61
  | MenhirState59
  | MenhirState57
  | MenhirState53
  | MenhirState50
  | MenhirState47
  | MenhirState46
  | MenhirState44
  | MenhirState43
  | MenhirState42
  | MenhirState40
  | MenhirState38
  | MenhirState33
  | MenhirState32
  | MenhirState24
  | MenhirState21
  | MenhirState18
  | MenhirState14
  | MenhirState13
  | MenhirState11
  | MenhirState7
  | MenhirState5
  | MenhirState2
  | MenhirState1
  | MenhirState0

# 29 "src/parsers/why_parser.mly"
  
  [@@@ocaml.warning "-33"]
  open AltErgoLib
  open Options
  open Parsed_interface

# 265 "src/parsers/why_parser.ml"

let rec _menhir_goto_bound : _menhir_env -> 'ttv_tail -> _menhir_state -> (AltErgoLib.Parsed.lexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState214 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ID _v ->
                _menhir_run222 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState224 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | INTEGER _v ->
                _menhir_run221 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState224 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MINUS ->
                _menhir_run218 _menhir_env (Obj.magic _menhir_stack) MenhirState224 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NUM _v ->
                _menhir_run217 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState224 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | QM ->
                _menhir_run216 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState224 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | QM_ID _v ->
                _menhir_run215 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState224 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState224)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState224 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LEFTSQ ->
            _menhir_run213 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState225 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | RIGHTSQ ->
            _menhir_run212 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState225
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState225)
    | _ ->
        _menhir_fail ()

and _menhir_reduce32 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (AltErgoLib.Parsed.lexpr list) = 
# 445 "src/parsers/why_parser.mly"
    ( [] )
# 324 "src/parsers/why_parser.ml"
     in
    _menhir_goto_filters _menhir_env _menhir_stack _menhir_s _v

and _menhir_run109 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHECK ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState109 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CUT ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState109 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DISTINCT ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState109 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXISTS ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState109 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState109 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FORALL ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState109 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState109 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState109 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState109 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState109 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState109 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTSQ ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState109 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LET ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState109 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState109 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState109 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState109 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState109 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRING _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState109 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState109 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState109 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState109

and _menhir_goto_list1_trigger_sep_bar : _menhir_env -> 'ttv_tail -> _menhir_state -> ((AltErgoLib.Parsed.lexpr list * bool) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState204 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (trig : (AltErgoLib.Parsed.lexpr list * bool))), _, (trigs : ((AltErgoLib.Parsed.lexpr list * bool) list))) = _menhir_stack in
        let _2 = () in
        let _v : ((AltErgoLib.Parsed.lexpr list * bool) list) = 
# 453 "src/parsers/why_parser.mly"
                                                   ( trig :: trigs )
# 391 "src/parsers/why_parser.ml"
         in
        _menhir_goto_list1_trigger_sep_bar _menhir_env _menhir_stack _menhir_s _v
    | MenhirState105 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RIGHTSQ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _endpos__1_, _menhir_s, _startpos__1_), _, (trigs : ((AltErgoLib.Parsed.lexpr list * bool) list))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : ((AltErgoLib.Parsed.lexpr list * bool) list) = 
# 440 "src/parsers/why_parser.mly"
                                                ( trigs )
# 411 "src/parsers/why_parser.ml"
             in
            _menhir_goto_triggers _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_run215 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 39 "src/parsers/why_parser.mly"
       (string)
# 426 "src/parsers/why_parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos_id_ = _endpos in
    let (id : (
# 39 "src/parsers/why_parser.mly"
       (string)
# 435 "src/parsers/why_parser.ml"
    )) = _v in
    let _startpos_id_ = _startpos in
    let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_id_ in
    let _startpos = _startpos_id_ in
    
# 491 "src/parsers/why_parser.mly"
                     ( mk_var (_startpos, _endpos) id )
# 443 "src/parsers/why_parser.ml"
     in
    _menhir_goto_bound _menhir_env _menhir_stack _menhir_s _v

and _menhir_run216 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _1 = () in
    let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos__1_ in
    let _startpos = _startpos__1_ in
    
# 490 "src/parsers/why_parser.mly"
                     ( mk_var (_startpos, _endpos) "?" )
# 459 "src/parsers/why_parser.ml"
     in
    _menhir_goto_bound _menhir_env _menhir_stack _menhir_s _v

and _menhir_run217 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 41 "src/parsers/why_parser.mly"
       (Num.num)
# 466 "src/parsers/why_parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos_i_ = _endpos in
    let (i : (
# 41 "src/parsers/why_parser.mly"
       (Num.num)
# 475 "src/parsers/why_parser.ml"
    )) = _v in
    let _startpos_i_ = _startpos in
    let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_i_ in
    let _startpos = _startpos_i_ in
    
# 494 "src/parsers/why_parser.mly"
                     ( mk_real_const (_startpos, _endpos) i )
# 483 "src/parsers/why_parser.ml"
     in
    _menhir_goto_bound _menhir_env _menhir_stack _menhir_s _v

and _menhir_run218 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | INTEGER _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos_i_ = _endpos in
        let (i : (
# 40 "src/parsers/why_parser.mly"
       (string)
# 503 "src/parsers/why_parser.ml"
        )) = _v in
        let _startpos_i_ = _startpos in
        let (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
        let _1 = () in
        let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_i_ in
        let _startpos = _startpos__1_ in
        
# 495 "src/parsers/why_parser.mly"
                     ( mk_int_const (_startpos, _endpos) i )
# 513 "src/parsers/why_parser.ml"
         in
        _menhir_goto_bound _menhir_env _menhir_stack _menhir_s _v
    | NUM _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos_i_ = _endpos in
        let (i : (
# 41 "src/parsers/why_parser.mly"
       (Num.num)
# 526 "src/parsers/why_parser.ml"
        )) = _v in
        let _startpos_i_ = _startpos in
        let (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
        let _1 = () in
        let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_i_ in
        let _startpos = _startpos__1_ in
        
# 496 "src/parsers/why_parser.mly"
                     ( mk_real_const (_startpos, _endpos) i )
# 536 "src/parsers/why_parser.ml"
         in
        _menhir_goto_bound _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run221 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 40 "src/parsers/why_parser.mly"
       (string)
# 549 "src/parsers/why_parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos_i_ = _endpos in
    let (i : (
# 40 "src/parsers/why_parser.mly"
       (string)
# 558 "src/parsers/why_parser.ml"
    )) = _v in
    let _startpos_i_ = _startpos in
    let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_i_ in
    let _startpos = _startpos_i_ in
    
# 493 "src/parsers/why_parser.mly"
                     ( mk_int_const (_startpos, _endpos) i )
# 566 "src/parsers/why_parser.ml"
     in
    _menhir_goto_bound _menhir_env _menhir_stack _menhir_s _v

and _menhir_run222 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 38 "src/parsers/why_parser.mly"
       (string)
# 573 "src/parsers/why_parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos_id_ = _endpos in
    let (id : (
# 38 "src/parsers/why_parser.mly"
       (string)
# 582 "src/parsers/why_parser.ml"
    )) = _v in
    let _startpos_id_ = _startpos in
    let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_id_ in
    let _startpos = _startpos_id_ in
    
# 492 "src/parsers/why_parser.mly"
                     ( mk_var (_startpos, _endpos) id )
# 590 "src/parsers/why_parser.ml"
     in
    _menhir_goto_bound _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_and_recursive_opt : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> ((AltErgoLib.Loc.t * string list * string *
   (string * (string * AltErgoLib.Parsed.ppure_type) list) list)
  list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v ->
    match _menhir_s with
    | MenhirState47 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos_others_ = _endpos in
        let (others : ((AltErgoLib.Loc.t * string list * string *
   (string * (string * AltErgoLib.Parsed.ppure_type) list) list)
  list)) = _v in
        let ((((_menhir_stack, _menhir_s, _startpos__1_), _, (ty_vars : (string list))), _endpos_ty_, _, (ty : (string)), _startpos_ty_), _endpos_enum_, _, (enum : ((string * (string * AltErgoLib.Parsed.ppure_type) list) list))) = _menhir_stack in
        let _4 = () in
        let _1 = () in
        let _endpos = _endpos_others_ in
        let _v : ((AltErgoLib.Loc.t * string list * string *
   (string * (string * AltErgoLib.Parsed.ppure_type) list) list)
  list) = let _endpos = _endpos_others_ in
        let _startpos = _startpos__1_ in
        
# 233 "src/parsers/why_parser.mly"
    ( ((_startpos, _endpos), ty_vars, ty, enum) :: others)
# 617 "src/parsers/why_parser.ml"
         in
        _menhir_goto_and_recursive_opt _menhir_env _menhir_stack _endpos _menhir_s _v
    | MenhirState42 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos_others_ = _endpos in
        let (others : ((AltErgoLib.Loc.t * string list * string *
   (string * (string * AltErgoLib.Parsed.ppure_type) list) list)
  list)) = _v in
        let ((((_menhir_stack, _menhir_s, _startpos__1_), _, (ty_vars : (string list))), _endpos_ty_, _, (ty : (string)), _startpos_ty_), _endpos_enum_, _, (enum : ((string * (string * AltErgoLib.Parsed.ppure_type) list) list))) = _menhir_stack in
        let _4 = () in
        let _1 = () in
        let _v : (AltErgoLib.Parsed.decl) = let _endpos = _endpos_others_ in
        let _startpos = _startpos__1_ in
        
# 109 "src/parsers/why_parser.mly"
    (
      match others with
        | [] ->
           mk_algebraic_type_decl (_startpos, _endpos) ty_vars ty enum
        | l ->
           let l = ((_startpos, _endpos), ty_vars, ty, enum) :: l in
           let l =
             List.map
               (fun (a, b, c, d) ->
                 match mk_algebraic_type_decl a b c d with
                 | Parsed.TypeDecl [e] -> e
                 | _ -> assert false
               ) l
           in
           mk_rec_type_decl l
    )
# 650 "src/parsers/why_parser.ml"
         in
        _menhir_goto_decl _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_triggers : _menhir_env -> 'ttv_tail -> _menhir_state -> ((AltErgoLib.Parsed.lexpr list * bool) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState107 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LEFTBR ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack) MenhirState108 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DOT ->
            _menhir_reduce32 _menhir_env (Obj.magic _menhir_stack) MenhirState108
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState108)
    | MenhirState104 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LEFTBR ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack) MenhirState232 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DOT ->
            _menhir_reduce32 _menhir_env (Obj.magic _menhir_stack) MenhirState232
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState232)
    | _ ->
        _menhir_fail ()

and _menhir_goto_list0_primitive_type_sep_comma : _menhir_env -> 'ttv_tail -> _menhir_state -> (AltErgoLib.Parsed.ppure_type list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | RIGHTARROW ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BITV ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState322
        | BOOL ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState322
        | ID _v ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState322 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | INT ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState322
        | LEFTPAR ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState322 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | PROP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_s = MenhirState322 in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let (_menhir_stack, _menhir_s, (ty_list : (AltErgoLib.Parsed.ppure_type list))) = _menhir_stack in
            let _3 = () in
            let _2 = () in
            let _endpos = _endpos__3_ in
            let _v : (AltErgoLib.Parsed.plogic_type) = 
# 188 "src/parsers/why_parser.mly"
   ( mk_logic_type ty_list None )
# 725 "src/parsers/why_parser.ml"
             in
            _menhir_goto_logic_type _menhir_env _menhir_stack _endpos _menhir_s _v
        | QUOTE ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState322 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | REAL ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState322
        | UNIT ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState322
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState322)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_list1_lexpr_or_dom_sep_comma : _menhir_env -> 'ttv_tail -> _menhir_state -> (AltErgoLib.Parsed.lexpr list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState352 | MenhirState105 | MenhirState204 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (terms : (AltErgoLib.Parsed.lexpr list)) = _v in
        let _v : (AltErgoLib.Parsed.lexpr list * bool) = 
# 457 "src/parsers/why_parser.mly"
   ( terms, true (* true <-> user-given trigger *) )
# 755 "src/parsers/why_parser.ml"
         in
        let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        (match _menhir_s with
        | MenhirState204 | MenhirState105 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BAR ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | CHECK ->
                    _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState204 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | CUT ->
                    _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState204 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | DISTINCT ->
                    _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState204 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | EXISTS ->
                    _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState204 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | FALSE ->
                    _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState204 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | FORALL ->
                    _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState204 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | ID _v ->
                    _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState204 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | IF ->
                    _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState204 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | INTEGER _v ->
                    _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState204 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LEFTBR ->
                    _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState204 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LEFTPAR ->
                    _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState204 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LEFTSQ ->
                    _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState204 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LET ->
                    _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState204 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | MATCH ->
                    _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState204 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | MINUS ->
                    _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState204 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | NOT ->
                    _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState204 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | NUM _v ->
                    _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState204 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | STRING _v ->
                    _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState204 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TRUE ->
                    _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState204 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | VOID ->
                    _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState204 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState204)
            | RIGHTSQ ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, (trig : (AltErgoLib.Parsed.lexpr list * bool))) = _menhir_stack in
                let _v : ((AltErgoLib.Parsed.lexpr list * bool) list) = 
# 452 "src/parsers/why_parser.mly"
                 ( [trig] )
# 819 "src/parsers/why_parser.ml"
                 in
                _menhir_goto_list1_trigger_sep_bar _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | MenhirState352 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | EOF ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, (trigger : (AltErgoLib.Parsed.lexpr list * bool))) = _menhir_stack in
                let _2 = () in
                let _v : (
# 76 "src/parsers/why_parser.mly"
      (AltErgoLib.Parsed.lexpr list * bool)
# 841 "src/parsers/why_parser.ml"
                ) = 
# 91 "src/parsers/why_parser.mly"
                        ( trigger )
# 845 "src/parsers/why_parser.ml"
                 in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_1 : (
# 76 "src/parsers/why_parser.mly"
      (AltErgoLib.Parsed.lexpr list * bool)
# 852 "src/parsers/why_parser.ml"
                )) = _v in
                Obj.magic _1
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            _menhir_fail ())
    | MenhirState208 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (edl : (AltErgoLib.Parsed.lexpr list)) = _v in
        let (_menhir_stack, _menhir_s, (ed : (AltErgoLib.Parsed.lexpr))) = _menhir_stack in
        let _2 = () in
        let _v : (AltErgoLib.Parsed.lexpr list) = 
# 474 "src/parsers/why_parser.mly"
                                                             ( ed :: edl )
# 872 "src/parsers/why_parser.ml"
         in
        _menhir_goto_list1_lexpr_or_dom_sep_comma _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_sq : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (bool) -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState211 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ID _v ->
            _menhir_run222 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState214 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | INTEGER _v ->
            _menhir_run221 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState214 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MINUS ->
            _menhir_run218 _menhir_env (Obj.magic _menhir_stack) MenhirState214 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NUM _v ->
            _menhir_run217 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState214 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | QM ->
            _menhir_run216 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState214 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | QM_ID _v ->
            _menhir_run215 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState214 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState214)
    | MenhirState225 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((((_menhir_stack, _endpos_e_, _menhir_s, (e : (AltErgoLib.Parsed.lexpr)), _startpos_e_), _endpos_lbr_, _, (lbr : (bool))), _, (lbnd : (AltErgoLib.Parsed.lexpr))), _, (rbnd : (AltErgoLib.Parsed.lexpr))), _endpos_rbr_, _, (rbr : (bool))) = _menhir_stack in
        let _5 = () in
        let _2 = () in
        let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_rbr_ in
        let _startpos = _startpos_e_ in
        
# 480 "src/parsers/why_parser.mly"
   ( mk_in_interval (_startpos, _endpos) e lbr lbnd rbnd rbr )
# 914 "src/parsers/why_parser.ml"
         in
        _menhir_goto_lexpr_or_dom _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_list0_lexpr_sep_comma : _menhir_env -> 'ttv_tail -> _menhir_state -> (AltErgoLib.Parsed.lexpr list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState133 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RIGHTPAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let (((_menhir_stack, _endpos_app_, _menhir_s, (app : (string)), _startpos_app_), _startpos__2_), _, (args : (AltErgoLib.Parsed.lexpr list))) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _startpos = _startpos_app_ in
            let _endpos = _endpos__4_ in
            let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos__4_ in
            let _startpos = _startpos_app_ in
            
# 397 "src/parsers/why_parser.mly"
   ( mk_application (_startpos, _endpos) app args )
# 945 "src/parsers/why_parser.ml"
             in
            _menhir_goto_simple_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState197 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RIGHTBR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__5_ = _endpos in
            let (((_menhir_stack, _menhir_s, _startpos__1_), _endpos_filt_, _, (filt : (AltErgoLib.Parsed.lexpr)), _startpos_filt_), _, (filt_l : (AltErgoLib.Parsed.lexpr list))) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : (AltErgoLib.Parsed.lexpr list) = 
# 449 "src/parsers/why_parser.mly"
   ( filt :: filt_l )
# 972 "src/parsers/why_parser.ml"
             in
            _menhir_goto_filters _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_reduce7 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let (_, _endpos) = Obj.magic _menhir_stack in
    let _v : ((AltErgoLib.Loc.t * string list * string *
   (string * (string * AltErgoLib.Parsed.ppure_type) list) list)
  list) = 
# 230 "src/parsers/why_parser.mly"
    ( [] )
# 992 "src/parsers/why_parser.ml"
     in
    _menhir_goto_and_recursive_opt _menhir_env _menhir_stack _endpos _menhir_s _v

and _menhir_run43 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LEFTPAR ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState43 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | QUOTE ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState43 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _ ->
        _menhir_reduce164 _menhir_env (Obj.magic _menhir_stack) MenhirState43
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState43

and _menhir_goto_list0_logic_binder_sep_comma : _menhir_env -> 'ttv_tail -> _menhir_state -> ((AltErgoLib.Loc.t * string * AltErgoLib.Parsed.ppure_type) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState298 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RIGHTPAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | EQUAL ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | CHECK ->
                    _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState308 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | CUT ->
                    _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState308 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | DISTINCT ->
                    _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState308 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | EXISTS ->
                    _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState308 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | FALSE ->
                    _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState308 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | FORALL ->
                    _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState308 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | ID _v ->
                    _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState308 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | IF ->
                    _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState308 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | INTEGER _v ->
                    _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState308 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LEFTBR ->
                    _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState308 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LEFTPAR ->
                    _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState308 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LEFTSQ ->
                    _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState308 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LET ->
                    _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState308 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | MATCH ->
                    _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState308 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | MINUS ->
                    _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState308 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | NOT ->
                    _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState308 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | NUM _v ->
                    _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState308 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | STRING _v ->
                    _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState308 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TRUE ->
                    _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState308 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | VOID ->
                    _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState308 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState308)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState331 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RIGHTPAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | COLON ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | BITV ->
                    _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState334
                | BOOL ->
                    _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState334
                | ID _v ->
                    _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState334 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | INT ->
                    _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState334
                | LEFTPAR ->
                    _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState334 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | QUOTE ->
                    _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState334 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | REAL ->
                    _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState334
                | UNIT ->
                    _menhir_run22 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState334
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState334)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_reduce161 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : ((AltErgoLib.Parsed.lexpr list * bool) list) = 
# 439 "src/parsers/why_parser.mly"
                                        ( [] )
# 1147 "src/parsers/why_parser.ml"
     in
    _menhir_goto_triggers _menhir_env _menhir_stack _menhir_s _v

and _menhir_run105 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHECK ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CUT ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DISTINCT ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXISTS ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FORALL ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState105 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState105 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTSQ ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LET ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState105 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRING _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState105

and _menhir_goto_list1_primitive_type_sep_comma : _menhir_env -> 'ttv_tail -> _menhir_state -> (AltErgoLib.Parsed.ppure_type list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState33 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _endpos_ty_, _menhir_s, (ty : (AltErgoLib.Parsed.ppure_type))), _), _, (ty_l : (AltErgoLib.Parsed.ppure_type list))) = _menhir_stack in
        let _2 = () in
        let _v : (AltErgoLib.Parsed.ppure_type list) = 
# 200 "src/parsers/why_parser.mly"
                                                                  ( ty::ty_l )
# 1214 "src/parsers/why_parser.ml"
         in
        _menhir_goto_list1_primitive_type_sep_comma _menhir_env _menhir_stack _menhir_s _v
    | MenhirState24 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RIGHTPAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState38 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState38)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState316 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (ty_l : (AltErgoLib.Parsed.ppure_type list))) = _menhir_stack in
        let _v : (AltErgoLib.Parsed.ppure_type list) = 
# 204 "src/parsers/why_parser.mly"
                                        ( ty_l )
# 1248 "src/parsers/why_parser.ml"
         in
        _menhir_goto_list0_primitive_type_sep_comma _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_reduce78 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : ((AltErgoLib.Loc.t * string * AltErgoLib.Parsed.ppure_type) list) = 
# 207 "src/parsers/why_parser.mly"
                                           ( [] )
# 1259 "src/parsers/why_parser.ml"
     in
    _menhir_goto_list0_logic_binder_sep_comma _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_list1_named_ident_sep_comma : _menhir_env -> 'ttv_tail -> _menhir_state -> ((string * string) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState96 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (id : (string * string))), _, (l : ((string * string) list))) = _menhir_stack in
        let _2 = () in
        let _v : ((string * string) list) = 
# 546 "src/parsers/why_parser.mly"
                                                                ( id :: l )
# 1275 "src/parsers/why_parser.ml"
         in
        _menhir_goto_list1_named_ident_sep_comma _menhir_env _menhir_stack _menhir_s _v
    | MenhirState106 | MenhirState92 | MenhirState99 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BITV ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState101
            | BOOL ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState101
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState101 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | INT ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState101
            | LEFTPAR ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState101 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | QUOTE ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState101 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | REAL ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState101
            | UNIT ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState101
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState101)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState314 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BITV ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState316
            | BOOL ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState316
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState316 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | INT ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState316
            | LEFTPAR ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState316 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | PROP ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let _menhir_s = MenhirState316 in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos__1_ = _endpos in
                let _1 = () in
                let _endpos = _endpos__1_ in
                let _v : (AltErgoLib.Parsed.plogic_type) = 
# 190 "src/parsers/why_parser.mly"
       ( mk_logic_type [] None )
# 1346 "src/parsers/why_parser.ml"
                 in
                _menhir_goto_logic_type _menhir_env _menhir_stack _endpos _menhir_s _v
            | QUOTE ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState316 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | REAL ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState316
            | UNIT ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState316
            | RIGHTARROW ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_s = MenhirState316 in
                let _v : (AltErgoLib.Parsed.ppure_type list) = 
# 203 "src/parsers/why_parser.mly"
                                        ( [] )
# 1361 "src/parsers/why_parser.ml"
                 in
                _menhir_goto_list0_primitive_type_sep_comma _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState316)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_list1_lexpr_sep_pv : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (AltErgoLib.Parsed.lexpr list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v ->
    match _menhir_s with
    | MenhirState291 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos_body_ = _endpos in
        let (body : (AltErgoLib.Parsed.lexpr list)) = _v in
        let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos_name_, _, (name : (string)), _startpos_name_) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : (AltErgoLib.Parsed.decl) = let _endpos = _endpos_body_ in
        let _startpos = _startpos__1_ in
        
# 148 "src/parsers/why_parser.mly"
   ( mk_rewriting (_startpos, _endpos) name body )
# 1393 "src/parsers/why_parser.ml"
         in
        _menhir_goto_decl _menhir_env _menhir_stack _menhir_s _v
    | MenhirState294 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos_e_l_ = _endpos in
        let (e_l : (AltErgoLib.Parsed.lexpr list)) = _v in
        let ((_menhir_stack, _endpos_e_, _menhir_s, (e : (AltErgoLib.Parsed.lexpr)), _startpos_e_), _endpos__2_) = _menhir_stack in
        let _2 = () in
        let _endpos = _endpos_e_l_ in
        let _v : (AltErgoLib.Parsed.lexpr list) = 
# 462 "src/parsers/why_parser.mly"
                                         ( e :: e_l )
# 1407 "src/parsers/why_parser.ml"
         in
        _menhir_goto_list1_lexpr_sep_pv _menhir_env _menhir_stack _endpos _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_theory_elt : _menhir_env -> 'ttv_tail -> _menhir_state -> (AltErgoLib.Parsed.decl) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AXIOM ->
        _menhir_run281 _menhir_env (Obj.magic _menhir_stack) MenhirState287 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CASESPLIT ->
        _menhir_run62 _menhir_env (Obj.magic _menhir_stack) MenhirState287 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | END ->
        _menhir_reduce157 _menhir_env (Obj.magic _menhir_stack) MenhirState287
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState287

and _menhir_goto_list1_match_cases : _menhir_env -> 'ttv_tail -> _menhir_state -> ((AltErgoLib.Parsed.pattern * AltErgoLib.Parsed.lexpr) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BAR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ID _v ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState273 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState273)
    | END ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos__5_ = _endpos in
        let (((_menhir_stack, _menhir_s, _startpos__1_), _endpos_e_, _, (e : (AltErgoLib.Parsed.lexpr)), _startpos_e_), _, (cases : ((AltErgoLib.Parsed.pattern * AltErgoLib.Parsed.lexpr) list))) = _menhir_stack in
        let _5 = () in
        let _3 = () in
        let _1 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos__5_ in
        let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos__5_ in
        let _startpos = _startpos__1_ in
        
# 356 "src/parsers/why_parser.mly"
    ( mk_match (_startpos, _endpos) e (List.rev cases) )
# 1466 "src/parsers/why_parser.ml"
         in
        _menhir_goto_lexpr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_let_binders : _menhir_env -> 'ttv_tail -> _menhir_state -> ((string * AltErgoLib.Parsed.lexpr) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState73 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | IN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | CHECK ->
                _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | CUT ->
                _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DISTINCT ->
                _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | EXISTS ->
                _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FALSE ->
                _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState75 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FORALL ->
                _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState75 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | IF ->
                _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | INTEGER _v ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState75 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTBR ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTPAR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTSQ ->
                _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState75 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LET ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MATCH ->
                _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MINUS ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NOT ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NUM _v ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState75 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | STRING _v ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TRUE ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState75 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | VOID ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState75 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState75)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState253 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _endpos_binder_, _menhir_s, (binder : (string)), _startpos_binder_), _endpos_e_, _, (e : (AltErgoLib.Parsed.lexpr)), _startpos_e_), _, (l : ((string * AltErgoLib.Parsed.lexpr) list))) = _menhir_stack in
        let _4 = () in
        let _2 = () in
        let _v : ((string * AltErgoLib.Parsed.lexpr) list) = 
# 373 "src/parsers/why_parser.mly"
                                                       ( (binder, e) :: l )
# 1549 "src/parsers/why_parser.ml"
         in
        _menhir_goto_let_binders _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_list1_label_expr_sep_PV : _menhir_env -> 'ttv_tail -> _menhir_state -> ((string * AltErgoLib.Parsed.lexpr) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState86 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RIGHTBR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__5_ = _endpos in
            let (((_menhir_stack, _menhir_s, _startpos__1_), _endpos_se_, _, (se : (AltErgoLib.Parsed.lexpr)), _startpos_se_), _, (labels : ((string * AltErgoLib.Parsed.lexpr) list))) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__5_ in
            let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos__5_ in
            let _startpos = _startpos__1_ in
            
# 389 "src/parsers/why_parser.mly"
   ( mk_with_record (_startpos, _endpos) se labels )
# 1581 "src/parsers/why_parser.ml"
             in
            _menhir_goto_simple_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState242 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((_menhir_stack, _endpos_id_, _menhir_s, (id : (string)), _startpos_id_), _endpos_e_, _, (e : (AltErgoLib.Parsed.lexpr)), _startpos_e_), _endpos__4_), _, (l : ((string * AltErgoLib.Parsed.lexpr) list))) = _menhir_stack in
        let _4 = () in
        let _2 = () in
        let _v : ((string * AltErgoLib.Parsed.lexpr) list) = 
# 517 "src/parsers/why_parser.mly"
   ( (id, e) :: l )
# 1599 "src/parsers/why_parser.ml"
         in
        _menhir_goto_list1_label_expr_sep_PV _menhir_env _menhir_stack _menhir_s _v
    | MenhirState82 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RIGHTBR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _menhir_s, _startpos__1_), _, (labels : ((string * AltErgoLib.Parsed.lexpr) list))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__3_ in
            let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos__3_ in
            let _startpos = _startpos__1_ in
            
# 386 "src/parsers/why_parser.mly"
   ( mk_record (_startpos, _endpos) labels )
# 1623 "src/parsers/why_parser.ml"
             in
            _menhir_goto_simple_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_lexpr_or_dom : _menhir_env -> 'ttv_tail -> _menhir_state -> (AltErgoLib.Parsed.lexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | COMMA ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | CHECK ->
            _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState208 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | CUT ->
            _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState208 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DISTINCT ->
            _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState208 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | EXISTS ->
            _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState208 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | FALSE ->
            _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState208 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | FORALL ->
            _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState208 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | ID _v ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState208 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | IF ->
            _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState208 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | INTEGER _v ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState208 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LEFTBR ->
            _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState208 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LEFTPAR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState208 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LEFTSQ ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState208 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LET ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState208 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MATCH ->
            _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState208 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MINUS ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState208 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOT ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState208 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NUM _v ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState208 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | STRING _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState208 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TRUE ->
            _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState208 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | VOID ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState208 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState208)
    | BAR | EOF | RIGHTSQ ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (ed : (AltErgoLib.Parsed.lexpr))) = _menhir_stack in
        let _v : (AltErgoLib.Parsed.lexpr list) = 
# 473 "src/parsers/why_parser.mly"
                                                ( [ed] )
# 1697 "src/parsers/why_parser.ml"
         in
        _menhir_goto_list1_lexpr_or_dom_sep_comma _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run212 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _1 = () in
    let _endpos = _endpos__1_ in
    let _v : (bool) = 
# 487 "src/parsers/why_parser.mly"
          (false)
# 1717 "src/parsers/why_parser.ml"
     in
    _menhir_goto_sq _menhir_env _menhir_stack _endpos _menhir_s _v

and _menhir_run213 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _1 = () in
    let _endpos = _endpos__1_ in
    let _v : (bool) = 
# 486 "src/parsers/why_parser.mly"
         (true)
# 1732 "src/parsers/why_parser.ml"
     in
    _menhir_goto_sq _menhir_env _menhir_stack _endpos _menhir_s _v

and _menhir_goto_filters : _menhir_env -> 'ttv_tail -> _menhir_state -> (AltErgoLib.Parsed.lexpr list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState108 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DOT ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | CHECK ->
                _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState201 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | CUT ->
                _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState201 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DISTINCT ->
                _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState201 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | EXISTS ->
                _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState201 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FALSE ->
                _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState201 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FORALL ->
                _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState201 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState201 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | IF ->
                _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState201 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | INTEGER _v ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState201 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTBR ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState201 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTPAR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState201 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTSQ ->
                _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState201 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LET ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState201 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MATCH ->
                _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState201 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MINUS ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState201 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NOT ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState201 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NUM _v ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState201 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | STRING _v ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState201 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TRUE ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState201 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | VOID ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState201 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState201)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState232 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DOT ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | CHECK ->
                _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState234 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | CUT ->
                _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState234 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DISTINCT ->
                _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState234 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | EXISTS ->
                _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState234 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FALSE ->
                _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState234 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FORALL ->
                _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState234 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState234 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | IF ->
                _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState234 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | INTEGER _v ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState234 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTBR ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState234 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTPAR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState234 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTSQ ->
                _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState234 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LET ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState234 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MATCH ->
                _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState234 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MINUS ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState234 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NOT ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState234 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NUM _v ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState234 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | STRING _v ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState234 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TRUE ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState234 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | VOID ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState234 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState234)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_list2_lexpr_sep_comma : _menhir_env -> 'ttv_tail -> _menhir_state -> (AltErgoLib.Parsed.lexpr list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState111 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RIGHTPAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let (((_menhir_stack, _menhir_s, _startpos__1_), _startpos__2_), _, (dist_l : (AltErgoLib.Parsed.lexpr list))) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__4_ in
            let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos__4_ in
            let _startpos = _startpos__1_ in
            
# 315 "src/parsers/why_parser.mly"
   ( mk_distinct (_startpos, _endpos) dist_l )
# 1889 "src/parsers/why_parser.ml"
             in
            _menhir_goto_lexpr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState192 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _endpos_e_, _menhir_s, (e : (AltErgoLib.Parsed.lexpr)), _startpos_e_), _, (el : (AltErgoLib.Parsed.lexpr list))) = _menhir_stack in
        let _2 = () in
        let _v : (AltErgoLib.Parsed.lexpr list) = 
# 500 "src/parsers/why_parser.mly"
                                              ( e :: el   )
# 1906 "src/parsers/why_parser.ml"
         in
        _menhir_goto_list2_lexpr_sep_comma _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_run192 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (AltErgoLib.Parsed.lexpr) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHECK ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState192 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CUT ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState192 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DISTINCT ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState192 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXISTS ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState192 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState192 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FORALL ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState192 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState192 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState192 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState192 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState192 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState192 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTSQ ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState192 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LET ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState192 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState192 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState192 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState192 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState192 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRING _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState192 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState192 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState192 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState192

and _menhir_goto_array_assignements : _menhir_env -> 'ttv_tail -> _menhir_state -> ((AltErgoLib.Parsed.lexpr * AltErgoLib.Parsed.lexpr) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState120 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RIGHTSQ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let (((_menhir_stack, _endpos_se_, _menhir_s, (se : (AltErgoLib.Parsed.lexpr)), _startpos_se_), _endpos__2_, _startpos__2_), _, (assigns : ((AltErgoLib.Parsed.lexpr * AltErgoLib.Parsed.lexpr) list))) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _startpos = _startpos_se_ in
            let _endpos = _endpos__4_ in
            let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos__4_ in
            let _startpos = _startpos_se_ in
            
# 405 "src/parsers/why_parser.mly"
    (
      let acc, l =
        match assigns with
	| [] -> assert false
	| (i, v)::l -> mk_array_set (_startpos, _endpos) se i v, l
      in
      List.fold_left (fun acc (i,v) ->
          mk_array_set (_startpos, _endpos) acc i v) acc l
    )
# 1995 "src/parsers/why_parser.ml"
             in
            _menhir_goto_simple_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState180 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (assign : (AltErgoLib.Parsed.lexpr * AltErgoLib.Parsed.lexpr))), _, (assign_l : ((AltErgoLib.Parsed.lexpr * AltErgoLib.Parsed.lexpr) list))) = _menhir_stack in
        let _2 = () in
        let _v : ((AltErgoLib.Parsed.lexpr * AltErgoLib.Parsed.lexpr) list) = 
# 433 "src/parsers/why_parser.mly"
   ( assign :: assign_l )
# 2012 "src/parsers/why_parser.ml"
         in
        _menhir_goto_array_assignements _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_list1_lexpr_sep_comma : _menhir_env -> 'ttv_tail -> _menhir_state -> (AltErgoLib.Parsed.lexpr list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState197 | MenhirState133 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (l : (AltErgoLib.Parsed.lexpr list)) = _v in
        let _v : (AltErgoLib.Parsed.lexpr list) = 
# 466 "src/parsers/why_parser.mly"
                            ( l )
# 2028 "src/parsers/why_parser.ml"
         in
        _menhir_goto_list0_lexpr_sep_comma _menhir_env _menhir_stack _menhir_s _v
    | MenhirState172 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (l : (AltErgoLib.Parsed.lexpr list)) = _v in
        let (_menhir_stack, _endpos_e_, _menhir_s, (e : (AltErgoLib.Parsed.lexpr)), _startpos_e_) = _menhir_stack in
        let _2 = () in
        let _v : (AltErgoLib.Parsed.lexpr list) = 
# 470 "src/parsers/why_parser.mly"
                                            ( e :: l )
# 2040 "src/parsers/why_parser.ml"
         in
        _menhir_goto_list1_lexpr_sep_comma _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_run122 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (AltErgoLib.Parsed.lexpr) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHECK ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CUT ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DISTINCT ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXISTS ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState122 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FORALL ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState122 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState122 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTSQ ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState122 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LET ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState122 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRING _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState122 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState122 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState122

and _menhir_run124 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (AltErgoLib.Parsed.lexpr) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHECK ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState124 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CUT ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState124 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DISTINCT ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState124 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXISTS ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState124 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState124 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FORALL ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState124 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState124 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState124 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState124 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState124 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState124 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTSQ ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState124 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LET ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState124 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState124 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState124 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState124 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState124 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRING _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState124 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState124 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState124 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState124

and _menhir_run138 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (AltErgoLib.Parsed.lexpr) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHECK ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState138 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CUT ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState138 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DISTINCT ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState138 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXISTS ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState138 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState138 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FORALL ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState138 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState138 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState138 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState138 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState138 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState138 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTSQ ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState138 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LET ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState138 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState138 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState138 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState138 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState138 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRING _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState138 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState138 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState138 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState138

and _menhir_run140 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (AltErgoLib.Parsed.lexpr) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHECK ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState140 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CUT ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState140 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DISTINCT ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState140 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXISTS ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState140 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState140 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FORALL ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState140 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState140 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState140 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState140 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState140 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState140 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTSQ ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState140 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LET ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState140 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState140 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState140 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState140 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState140 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRING _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState140 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState140 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState140 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState140

and _menhir_run142 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (AltErgoLib.Parsed.lexpr) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHECK ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState142 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CUT ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState142 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DISTINCT ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState142 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXISTS ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState142 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState142 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FORALL ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState142 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState142 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState142 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState142 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState142 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState142 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTSQ ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState142 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LET ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState142 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState142 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState142 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState142 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState142 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRING _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState142 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState142 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState142 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState142

and _menhir_run144 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (AltErgoLib.Parsed.lexpr) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHECK ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState144 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CUT ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState144 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DISTINCT ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState144 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXISTS ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState144 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState144 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FORALL ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState144 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState144 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState144 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState144 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState144 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState144 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTSQ ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState144 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LET ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState144 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState144 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState144 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState144 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState144 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRING _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState144 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState144 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState144 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState144

and _menhir_run146 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (AltErgoLib.Parsed.lexpr) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHECK ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CUT ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DISTINCT ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXISTS ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FORALL ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState146 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState146 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTSQ ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LET ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState146 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRING _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState146 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState146

and _menhir_run148 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (AltErgoLib.Parsed.lexpr) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHECK ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CUT ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DISTINCT ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXISTS ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FORALL ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState148 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState148 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTSQ ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LET ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState148 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRING _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState148

and _menhir_run152 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (AltErgoLib.Parsed.lexpr) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHECK ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState152 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CUT ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState152 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DISTINCT ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState152 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXISTS ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState152 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState152 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FORALL ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState152 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState152 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState152 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState152 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState152 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState152 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTSQ ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState152 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LET ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState152 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState152 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState152 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState152 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState152 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRING _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState152 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState152 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState152 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState152

and _menhir_run154 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (AltErgoLib.Parsed.lexpr) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHECK ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CUT ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DISTINCT ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXISTS ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FORALL ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState154 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState154 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTSQ ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LET ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState154 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRING _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState154 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState154

and _menhir_run156 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (AltErgoLib.Parsed.lexpr) * Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _startpos ->
    let _menhir_stack = (_menhir_stack, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHECK ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CUT ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DISTINCT ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXISTS ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState156 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FORALL ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState156 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState156 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTSQ ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState156 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LET ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState156 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRING _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState156 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState156 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState156

and _menhir_run158 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (AltErgoLib.Parsed.lexpr) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHECK ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState158 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CUT ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState158 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DISTINCT ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState158 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXISTS ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState158 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState158 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FORALL ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState158 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState158 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState158 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState158 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState158 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState158 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTSQ ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState158 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LET ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState158 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState158 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState158 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState158 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState158 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRING _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState158 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState158 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState158 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState158

and _menhir_run170 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (AltErgoLib.Parsed.lexpr) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHECK ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState170 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CUT ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState170 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DISTINCT ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState170 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXISTS ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState170 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState170 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FORALL ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState170 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState170 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState170 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState170 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState170 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState170 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTSQ ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState170 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LET ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState170 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState170 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState170 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState170 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState170 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRING _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState170 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState170 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState170 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState170

and _menhir_run175 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (AltErgoLib.Parsed.lexpr) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHECK ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState175 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CUT ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState175 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DISTINCT ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState175 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXISTS ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState175 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState175 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FORALL ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState175 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState175 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState175 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState175 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState175 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState175 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTSQ ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState175 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LET ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState175 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState175 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState175 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState175 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState175 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRING _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState175 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState175 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState175 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState175

and _menhir_run160 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (AltErgoLib.Parsed.lexpr) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHECK ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState160 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CUT ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState160 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DISTINCT ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState160 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXISTS ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState160 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState160 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FORALL ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState160 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState160 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState160 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState160 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState160 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState160 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTSQ ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState160 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LET ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState160 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState160 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState160 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState160 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState160 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRING _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState160 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState160 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState160 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState160

and _menhir_run126 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (AltErgoLib.Parsed.lexpr) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LEFTBR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | INTEGER _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | COMMA ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | INTEGER _v ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                    let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                    let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | RIGHTBR ->
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                        let _menhir_env = _menhir_discard _menhir_env in
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let _endpos__7_ = _endpos in
                        let ((((_menhir_stack, _endpos_e_, _menhir_s, (e : (AltErgoLib.Parsed.lexpr)), _startpos_e_), _startpos__3_), _endpos_i_, (i : (
# 40 "src/parsers/why_parser.mly"
       (string)
# 2839 "src/parsers/why_parser.ml"
                        )), _startpos_i_), _endpos_j_, (j : (
# 40 "src/parsers/why_parser.mly"
       (string)
# 2843 "src/parsers/why_parser.ml"
                        )), _startpos_j_) = _menhir_stack in
                        let _7 = () in
                        let _5 = () in
                        let _3 = () in
                        let _2 = () in
                        let _startpos = _startpos_e_ in
                        let _endpos = _endpos__7_ in
                        let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos__7_ in
                        let _startpos = _startpos_e_ in
                        
# 307 "src/parsers/why_parser.mly"
   ( mk_bitv_extract (_startpos, _endpos) e i j )
# 2856 "src/parsers/why_parser.ml"
                         in
                        _menhir_goto_lexpr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let ((((_menhir_stack, _, _menhir_s, _, _), _), _, _, _), _, _, _) = _menhir_stack in
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (((_menhir_stack, _, _menhir_s, _, _), _), _, _, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (((_menhir_stack, _, _menhir_s, _, _), _), _, _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run162 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (AltErgoLib.Parsed.lexpr) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHECK ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState162 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CUT ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState162 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DISTINCT ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState162 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXISTS ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState162 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState162 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FORALL ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState162 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState162 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState162 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState162 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState162 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState162 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTSQ ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState162 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LET ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState162 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState162 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState162 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState162 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState162 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRING _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState162 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState162 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState162 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState162

and _menhir_run164 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (AltErgoLib.Parsed.lexpr) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHECK ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState164 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CUT ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState164 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DISTINCT ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState164 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXISTS ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState164 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState164 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FORALL ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState164 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState164 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState164 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState164 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState164 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState164 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTSQ ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState164 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LET ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState164 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState164 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState164 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState164 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState164 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRING _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState164 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState164 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState164 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState164

and _menhir_run166 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (AltErgoLib.Parsed.lexpr) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHECK ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CUT ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DISTINCT ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXISTS ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState166 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FORALL ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState166 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState166 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTSQ ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState166 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LET ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState166 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRING _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState166 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState166 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState166

and _menhir_run150 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (AltErgoLib.Parsed.lexpr) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHECK ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CUT ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DISTINCT ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXISTS ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FORALL ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState150 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState150 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTSQ ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LET ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState150 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRING _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState150

and _menhir_run168 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (AltErgoLib.Parsed.lexpr) * Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _startpos ->
    let _menhir_stack = (_menhir_stack, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHECK ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState168 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CUT ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState168 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DISTINCT ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState168 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXISTS ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState168 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState168 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FORALL ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState168 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState168 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState168 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState168 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState168 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState168 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTSQ ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState168 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LET ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState168 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState168 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState168 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState168 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState168 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRING _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState168 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState168 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState168 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState168

and _menhir_reduce76 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (AltErgoLib.Parsed.lexpr list) = 
# 465 "src/parsers/why_parser.mly"
                        ( [] )
# 3146 "src/parsers/why_parser.ml"
     in
    _menhir_goto_list0_lexpr_sep_comma _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_theory_elts : _menhir_env -> 'ttv_tail -> _menhir_state -> (AltErgoLib.Parsed.decl list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState61 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | END ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__7_ = _endpos in
            let ((((_menhir_stack, _menhir_s, _startpos__1_), _endpos_th_id_, _, (th_id : (string)), _startpos_th_id_), _endpos_th_ext_, _, (th_ext : (string)), _startpos_th_ext_), _, (th_body : (AltErgoLib.Parsed.decl list))) = _menhir_stack in
            let _7 = () in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : (AltErgoLib.Parsed.decl) = let _endpos = _endpos__7_ in
            let _startpos = _startpos__1_ in
            
# 102 "src/parsers/why_parser.mly"
   ( mk_theory (_startpos, _endpos) th_id th_ext th_body )
# 3175 "src/parsers/why_parser.ml"
             in
            _menhir_goto_decl _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState287 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (th_elt : (AltErgoLib.Parsed.decl))), _, (th_rest : (AltErgoLib.Parsed.decl list))) = _menhir_stack in
        let _v : (AltErgoLib.Parsed.decl list) = 
# 155 "src/parsers/why_parser.mly"
                                            ( th_elt :: th_rest )
# 3191 "src/parsers/why_parser.ml"
         in
        _menhir_goto_theory_elts _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_list1_constructors_sep_bar : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> ((string * (string * AltErgoLib.Parsed.ppure_type) list) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState13 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState42 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AXIOM | EOF | FUNC | GOAL | LOGIC | PRED | REWRITING | THEORY | TYPE ->
            _menhir_reduce7 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState42)
    | MenhirState46 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState47 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AXIOM | EOF | FUNC | GOAL | LOGIC | PRED | REWRITING | THEORY | TYPE ->
            _menhir_reduce7 _menhir_env (Obj.magic _menhir_stack) MenhirState47
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState47)
    | MenhirState53 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _endpos_cons_, _menhir_s, (cons : (string)), _startpos_cons_), _endpos__2_, (_2 : ((string * AltErgoLib.Parsed.ppure_type) list))), _endpos_cons_l_, _, (cons_l : ((string * (string * AltErgoLib.Parsed.ppure_type) list) list))) = _menhir_stack in
        let _3 = () in
        let _endpos = _endpos_cons_l_ in
        let _v : ((string * (string * AltErgoLib.Parsed.ppure_type) list) list) = 
# 223 "src/parsers/why_parser.mly"
                                             ( (cons, _2) :: cons_l )
# 3236 "src/parsers/why_parser.ml"
         in
        _menhir_goto_list1_constructors_sep_bar _menhir_env _menhir_stack _endpos _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_list1_decl : _menhir_env -> 'ttv_tail -> _menhir_state -> (AltErgoLib.Parsed.file) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EOF ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (decls : (AltErgoLib.Parsed.file))) = _menhir_stack in
            let _2 = () in
            let _v : (
# 82 "src/parsers/why_parser.mly"
      (AltErgoLib.Parsed.file)
# 3259 "src/parsers/why_parser.ml"
            ) = 
# 87 "src/parsers/why_parser.mly"
                         ( decls )
# 3263 "src/parsers/why_parser.ml"
             in
            _menhir_goto_file_parser _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState346 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (decl : (AltErgoLib.Parsed.decl))), _, (decls : (AltErgoLib.Parsed.file))) = _menhir_stack in
        let _v : (AltErgoLib.Parsed.file) = 
# 98 "src/parsers/why_parser.mly"
                                 ( decl :: decls )
# 3279 "src/parsers/why_parser.ml"
         in
        _menhir_goto_list1_decl _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_logic_type : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (AltErgoLib.Parsed.plogic_type) -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos_ty_ = _endpos in
    let (ty : (AltErgoLib.Parsed.plogic_type)) = _v in
    let (((_menhir_stack, _menhir_s, _startpos__1_), (is_ac : (AltErgoLib.Symbols.name_kind))), _, (ids : ((string * string) list))) = _menhir_stack in
    let _4 = () in
    let _1 = () in
    let _v : (AltErgoLib.Parsed.decl) = let _endpos = _endpos_ty_ in
    let _startpos = _startpos__1_ in
    
# 131 "src/parsers/why_parser.mly"
   ( mk_logic (_startpos, _endpos) is_ac ids ty )
# 3299 "src/parsers/why_parser.ml"
     in
    _menhir_goto_decl _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_list1_logic_binder_sep_comma : _menhir_env -> 'ttv_tail -> _menhir_state -> ((AltErgoLib.Loc.t * string * AltErgoLib.Parsed.ppure_type) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState300 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (binders_list : ((AltErgoLib.Loc.t * string * AltErgoLib.Parsed.ppure_type) list)) = _v in
        let (_menhir_stack, _menhir_s, (binder : (AltErgoLib.Loc.t * string * AltErgoLib.Parsed.ppure_type))) = _menhir_stack in
        let _2 = () in
        let _v : ((AltErgoLib.Loc.t * string * AltErgoLib.Parsed.ppure_type) list) = 
# 214 "src/parsers/why_parser.mly"
   ( binder :: binders_list )
# 3315 "src/parsers/why_parser.ml"
         in
        _menhir_goto_list1_logic_binder_sep_comma _menhir_env _menhir_stack _menhir_s _v
    | MenhirState331 | MenhirState298 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (binders_l : ((AltErgoLib.Loc.t * string * AltErgoLib.Parsed.ppure_type) list)) = _v in
        let _v : ((AltErgoLib.Loc.t * string * AltErgoLib.Parsed.ppure_type) list) = 
# 208 "src/parsers/why_parser.mly"
                                           ( binders_l )
# 3325 "src/parsers/why_parser.ml"
         in
        _menhir_goto_list0_logic_binder_sep_comma _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_list1_multi_logic_binder : _menhir_env -> 'ttv_tail -> _menhir_state -> (((string * string) list * AltErgoLib.Parsed.ppure_type) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState99 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (binders : ((string * string) list * AltErgoLib.Parsed.ppure_type))), _, (l : (((string * string) list * AltErgoLib.Parsed.ppure_type) list))) = _menhir_stack in
        let _2 = () in
        let _v : (((string * string) list * AltErgoLib.Parsed.ppure_type) list) = 
# 542 "src/parsers/why_parser.mly"
   ( binders :: l )
# 3343 "src/parsers/why_parser.ml"
         in
        _menhir_goto_list1_multi_logic_binder _menhir_env _menhir_stack _menhir_s _v
    | MenhirState92 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LEFTSQ ->
            _menhir_run105 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState104 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DOT | LEFTBR ->
            _menhir_reduce161 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState104)
    | MenhirState106 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LEFTSQ ->
            _menhir_run105 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState107 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DOT | LEFTBR ->
            _menhir_reduce161 _menhir_env (Obj.magic _menhir_stack) MenhirState107
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState107)
    | _ ->
        _menhir_fail ()

and _menhir_goto_list1_label_sep_PV : _menhir_env -> 'ttv_tail -> _menhir_state -> ((string * AltErgoLib.Parsed.ppure_type) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState14 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RIGHTBR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _menhir_s, _startpos__1_), _, (labels : ((string * AltErgoLib.Parsed.ppure_type) list))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _endpos = _endpos__3_ in
            let _v : ((string * AltErgoLib.Parsed.ppure_type) list) = 
# 503 "src/parsers/why_parser.mly"
                                             ( labels )
# 3397 "src/parsers/why_parser.ml"
             in
            (match _menhir_s with
            | MenhirState13 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos_record_ = _endpos in
                let (record : ((string * AltErgoLib.Parsed.ppure_type) list)) = _v in
                let (((_menhir_stack, _menhir_s, _startpos__1_), _, (ty_vars : (string list))), _endpos_ty_, _, (ty : (string)), _startpos_ty_) = _menhir_stack in
                let _4 = () in
                let _1 = () in
                let _v : (AltErgoLib.Parsed.decl) = let _endpos = _endpos_record_ in
                let _startpos = _startpos__1_ in
                
# 127 "src/parsers/why_parser.mly"
   ( mk_record_type_decl (_startpos, _endpos) ty_vars ty record )
# 3413 "src/parsers/why_parser.ml"
                 in
                _menhir_goto_decl _menhir_env _menhir_stack _menhir_s _v
            | MenhirState50 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos__2_ = _endpos in
                let (_2 : ((string * AltErgoLib.Parsed.ppure_type) list)) = _v in
                let _1 = () in
                let _endpos = _endpos__2_ in
                let _v : ((string * AltErgoLib.Parsed.ppure_type) list) = 
# 227 "src/parsers/why_parser.mly"
                 ( _2 )
# 3426 "src/parsers/why_parser.ml"
                 in
                _menhir_goto_algebraic_args _menhir_env _menhir_stack _endpos _v
            | _ ->
                _menhir_fail ())
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState18 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s, (lt : (string * AltErgoLib.Parsed.ppure_type))), _endpos__2_), _, (list_lt : ((string * AltErgoLib.Parsed.ppure_type) list))) = _menhir_stack in
        let _2 = () in
        let _v : ((string * AltErgoLib.Parsed.ppure_type) list) = 
# 507 "src/parsers/why_parser.mly"
                                                         ( lt :: list_lt )
# 3445 "src/parsers/why_parser.ml"
         in
        _menhir_goto_list1_label_sep_PV _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_reduce106 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (AltErgoLib.Parsed.ppure_type) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _endpos_ty_, _menhir_s, (ty : (AltErgoLib.Parsed.ppure_type))) = _menhir_stack in
    let _v : (AltErgoLib.Parsed.ppure_type list) = 
# 199 "src/parsers/why_parser.mly"
                                                           ( [ty] )
# 3457 "src/parsers/why_parser.ml"
     in
    _menhir_goto_list1_primitive_type_sep_comma _menhir_env _menhir_stack _menhir_s _v

and _menhir_run33 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (AltErgoLib.Parsed.ppure_type) -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BITV ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | BOOL ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState33
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState33 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INT ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState33
    | LEFTPAR ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState33 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | QUOTE ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState33 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | REAL ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState33
    | UNIT ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState33
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState33

and _menhir_run115 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (AltErgoLib.Parsed.lexpr) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState115 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState115

and _menhir_run117 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (AltErgoLib.Parsed.lexpr) * Lexing.position -> Lexing.position -> (
# 39 "src/parsers/why_parser.mly"
       (string)
# 3503 "src/parsers/why_parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos_id_ = _endpos in
    let (id : (
# 39 "src/parsers/why_parser.mly"
       (string)
# 3512 "src/parsers/why_parser.ml"
    )) = _v in
    let _startpos_id_ = _startpos in
    let (_menhir_stack, _endpos_se_, _menhir_s, (se : (AltErgoLib.Parsed.lexpr)), _startpos_se_) = _menhir_stack in
    let _startpos = _startpos_se_ in
    let _endpos = _endpos_id_ in
    let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_id_ in
    let _startpos = _startpos_se_ in
    
# 425 "src/parsers/why_parser.mly"
    ( mk_algebraic_test (_startpos, _endpos) se id )
# 3523 "src/parsers/why_parser.ml"
     in
    _menhir_goto_simple_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run118 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (AltErgoLib.Parsed.lexpr) * Lexing.position -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState118 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState118

and _menhir_run120 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (AltErgoLib.Parsed.lexpr) * Lexing.position -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHECK ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CUT ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DISTINCT ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXISTS ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FORALL ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState120 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState120 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTSQ ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LET ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState120 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRING _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState120

and _menhir_run183 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (AltErgoLib.Parsed.lexpr) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState183 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState183

and _menhir_run185 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (AltErgoLib.Parsed.lexpr) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BITV ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState185
    | BOOL ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState185
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState185 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INT ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState185
    | LEFTPAR ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | QUOTE ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | REAL ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState185
    | UNIT ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState185
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState185

and _menhir_goto_named_ident : _menhir_env -> 'ttv_tail -> _menhir_state -> (string * string) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState314 | MenhirState106 | MenhirState99 | MenhirState96 | MenhirState92 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ID _v ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState96 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState96)
        | COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (id : (string * string))) = _menhir_stack in
            let _v : ((string * string) list) = 
# 545 "src/parsers/why_parser.mly"
                                                     ( [id] )
# 3655 "src/parsers/why_parser.ml"
             in
            _menhir_goto_list1_named_ident_sep_comma _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState296 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EQUAL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | CHECK ->
                _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState310 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | CUT ->
                _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState310 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DISTINCT ->
                _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState310 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | EXISTS ->
                _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState310 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FALSE ->
                _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState310 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FORALL ->
                _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState310 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState310 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | IF ->
                _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState310 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | INTEGER _v ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState310 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTBR ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState310 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTPAR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState310 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTSQ ->
                _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState310 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LET ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState310 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MATCH ->
                _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState310 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MINUS ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState310 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NOT ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState310 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NUM _v ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState310 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | STRING _v ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState310 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TRUE ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState310 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | VOID ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState310 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState310)
        | LEFTPAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState298 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | RIGHTPAR ->
                _menhir_reduce78 _menhir_env (Obj.magic _menhir_stack) MenhirState298
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState298)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState329 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LEFTPAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState331 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | RIGHTPAR ->
                _menhir_reduce78 _menhir_env (Obj.magic _menhir_stack) MenhirState331
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState331)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_reduce164 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (string list) = 
# 523 "src/parsers/why_parser.mly"
            ( [] )
# 3773 "src/parsers/why_parser.ml"
     in
    _menhir_goto_type_vars _menhir_env _menhir_stack _menhir_s _v

and _menhir_run5 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | QUOTE ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState5 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState5

and _menhir_goto_ac_modifier : _menhir_env -> 'ttv_tail -> (AltErgoLib.Symbols.name_kind) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState314 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState314

and _menhir_goto_lexpr : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (AltErgoLib.Parsed.lexpr) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState120 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LEFTARROW ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | LRARROW ->
            _menhir_run170 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTARROW ->
            _menhir_run140 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTSQ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let (((_menhir_stack, _endpos_se_, _menhir_s, (se : (AltErgoLib.Parsed.lexpr)), _startpos_se_), _endpos__2_, _startpos__2_), _endpos_e_, _, (e : (AltErgoLib.Parsed.lexpr)), _startpos_e_) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _startpos = _startpos_se_ in
            let _endpos = _endpos__4_ in
            let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos__4_ in
            let _startpos = _startpos_se_ in
            
# 402 "src/parsers/why_parser.mly"
   ( mk_array_get (_startpos, _endpos) se e )
# 3865 "src/parsers/why_parser.ml"
             in
            _menhir_goto_simple_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | XOR ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState122 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LRARROW ->
            _menhir_run170 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTARROW ->
            _menhir_run140 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | XOR ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AXIOM | BAR | CASESPLIT | COMMA | ELSE | END | EOF | FUNC | GOAL | IN | LEFTARROW | LOGIC | PRED | PV | REWRITING | RIGHTBR | RIGHTPAR | RIGHTSQ | THEN | THEORY | TYPE | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_se1_, _menhir_s, (se1 : (AltErgoLib.Parsed.lexpr)), _startpos_se1_), _endpos_se2_, _, (se2 : (AltErgoLib.Parsed.lexpr)), _startpos_se2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_se1_ in
            let _endpos = _endpos_se2_ in
            let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_se2_ in
            let _startpos = _startpos_se1_ in
            
# 269 "src/parsers/why_parser.mly"
   ( mk_xor (_startpos, _endpos) se1 se2 )
# 3936 "src/parsers/why_parser.ml"
             in
            _menhir_goto_lexpr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState124 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | AND | AT | AXIOM | BAR | CASESPLIT | COMMA | ELSE | END | EOF | EQUAL | FUNC | GE | GOAL | GT | IN | LE | LEFTARROW | LOGIC | LRARROW | LT | MINUS | NOTEQ | OR | PERCENT | PLUS | POW | POWDOT | PRED | PV | REWRITING | RIGHTARROW | RIGHTBR | RIGHTPAR | RIGHTSQ | SLASH | THEN | THEORY | TIMES | TYPE | WITH | XOR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_se1_, _menhir_s, (se1 : (AltErgoLib.Parsed.lexpr)), _startpos_se1_), _endpos_se2_, _, (se2 : (AltErgoLib.Parsed.lexpr)), _startpos_se2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_se1_ in
            let _endpos = _endpos_se2_ in
            let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_se2_ in
            let _startpos = _startpos_se1_ in
            
# 248 "src/parsers/why_parser.mly"
   ( mk_mul (_startpos, _endpos) se1 se2 )
# 3963 "src/parsers/why_parser.ml"
             in
            _menhir_goto_lexpr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState197 | MenhirState172 | MenhirState133 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | CHECK ->
                _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState172 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | CUT ->
                _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState172 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DISTINCT ->
                _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState172 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | EXISTS ->
                _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState172 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FALSE ->
                _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState172 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FORALL ->
                _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState172 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState172 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | IF ->
                _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState172 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | INTEGER _v ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState172 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTBR ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState172 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTPAR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState172 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTSQ ->
                _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState172 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LET ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState172 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MATCH ->
                _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState172 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MINUS ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState172 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NOT ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState172 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NUM _v ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState172 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | STRING _v ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState172 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TRUE ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState172 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | VOID ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState172 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState172)
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LRARROW ->
            _menhir_run170 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTARROW ->
            _menhir_run140 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | XOR ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTBR | RIGHTPAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _endpos_e_, _menhir_s, (e : (AltErgoLib.Parsed.lexpr)), _startpos_e_) = _menhir_stack in
            let _v : (AltErgoLib.Parsed.lexpr list) = 
# 469 "src/parsers/why_parser.mly"
                                            ( [e] )
# 4072 "src/parsers/why_parser.ml"
             in
            _menhir_goto_list1_lexpr_sep_comma _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState138 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | AND | AT | AXIOM | BAR | CASESPLIT | COMMA | ELSE | END | EOF | EQUAL | FUNC | GE | GOAL | GT | IN | LE | LEFTARROW | LOGIC | LRARROW | LT | MINUS | NOTEQ | OR | PERCENT | PLUS | POW | POWDOT | PRED | PV | REWRITING | RIGHTARROW | RIGHTBR | RIGHTPAR | RIGHTSQ | SLASH | THEN | THEORY | TIMES | TYPE | WITH | XOR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_se1_, _menhir_s, (se1 : (AltErgoLib.Parsed.lexpr)), _startpos_se1_), _endpos_se2_, _, (se2 : (AltErgoLib.Parsed.lexpr)), _startpos_se2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_se1_ in
            let _endpos = _endpos_se2_ in
            let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_se2_ in
            let _startpos = _startpos_se1_ in
            
# 251 "src/parsers/why_parser.mly"
   ( mk_div (_startpos, _endpos) se1 se2 )
# 4099 "src/parsers/why_parser.ml"
             in
            _menhir_goto_lexpr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState140 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LRARROW ->
            _menhir_run170 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTARROW ->
            _menhir_run140 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | XOR ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AXIOM | BAR | CASESPLIT | COMMA | ELSE | END | EOF | FUNC | GOAL | IN | LEFTARROW | LOGIC | PRED | PV | REWRITING | RIGHTBR | RIGHTPAR | RIGHTSQ | THEN | THEORY | TYPE | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_se1_, _menhir_s, (se1 : (AltErgoLib.Parsed.lexpr)), _startpos_se1_), _endpos_se2_, _, (se2 : (AltErgoLib.Parsed.lexpr)), _startpos_se2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_se1_ in
            let _endpos = _endpos_se2_ in
            let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_se2_ in
            let _startpos = _startpos_se1_ in
            
# 275 "src/parsers/why_parser.mly"
   ( mk_implies (_startpos, _endpos) se1 se2 )
# 4164 "src/parsers/why_parser.ml"
             in
            _menhir_goto_lexpr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState142 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | AND | AT | AXIOM | BAR | CASESPLIT | COMMA | ELSE | END | EOF | EQUAL | FUNC | GE | GOAL | GT | IN | LE | LEFTARROW | LOGIC | LRARROW | LT | MINUS | NOTEQ | OR | PERCENT | PLUS | POW | POWDOT | PRED | PV | REWRITING | RIGHTARROW | RIGHTBR | RIGHTPAR | RIGHTSQ | SLASH | THEN | THEORY | TIMES | TYPE | WITH | XOR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_se1_, _menhir_s, (se1 : (AltErgoLib.Parsed.lexpr)), _startpos_se1_), _endpos_se2_, _, (se2 : (AltErgoLib.Parsed.lexpr)), _startpos_se2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_se1_ in
            let _endpos = _endpos_se2_ in
            let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_se2_ in
            let _startpos = _startpos_se1_ in
            
# 260 "src/parsers/why_parser.mly"
   ( mk_pow_real (_startpos, _endpos) se1 se2 )
# 4191 "src/parsers/why_parser.ml"
             in
            _menhir_goto_lexpr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState144 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | AND | AT | AXIOM | BAR | CASESPLIT | COMMA | ELSE | END | EOF | EQUAL | FUNC | GE | GOAL | GT | IN | LE | LEFTARROW | LOGIC | LRARROW | LT | MINUS | NOTEQ | OR | PERCENT | PLUS | POW | POWDOT | PRED | PV | REWRITING | RIGHTARROW | RIGHTBR | RIGHTPAR | RIGHTSQ | SLASH | THEN | THEORY | TIMES | TYPE | WITH | XOR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_se1_, _menhir_s, (se1 : (AltErgoLib.Parsed.lexpr)), _startpos_se1_), _endpos_se2_, _, (se2 : (AltErgoLib.Parsed.lexpr)), _startpos_se2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_se1_ in
            let _endpos = _endpos_se2_ in
            let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_se2_ in
            let _startpos = _startpos_se1_ in
            
# 257 "src/parsers/why_parser.mly"
   ( mk_pow_int (_startpos, _endpos) se1 se2 )
# 4218 "src/parsers/why_parser.ml"
             in
            _menhir_goto_lexpr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState146 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AND | AXIOM | BAR | CASESPLIT | COMMA | ELSE | END | EOF | EQUAL | FUNC | GE | GOAL | GT | IN | LE | LEFTARROW | LOGIC | LRARROW | LT | MINUS | NOTEQ | OR | PLUS | PRED | PV | REWRITING | RIGHTARROW | RIGHTBR | RIGHTPAR | RIGHTSQ | THEN | THEORY | TYPE | WITH | XOR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_se1_, _menhir_s, (se1 : (AltErgoLib.Parsed.lexpr)), _startpos_se1_), _endpos_se2_, _, (se2 : (AltErgoLib.Parsed.lexpr)), _startpos_se2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_se1_ in
            let _endpos = _endpos_se2_ in
            let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_se2_ in
            let _startpos = _startpos_se1_ in
            
# 242 "src/parsers/why_parser.mly"
   ( mk_add (_startpos, _endpos) se1 se2 )
# 4257 "src/parsers/why_parser.ml"
             in
            _menhir_goto_lexpr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState148 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | AND | AT | AXIOM | BAR | CASESPLIT | COMMA | ELSE | END | EOF | EQUAL | FUNC | GE | GOAL | GT | IN | LE | LEFTARROW | LOGIC | LRARROW | LT | MINUS | NOTEQ | OR | PERCENT | PLUS | POW | POWDOT | PRED | PV | REWRITING | RIGHTARROW | RIGHTBR | RIGHTPAR | RIGHTSQ | SLASH | THEN | THEORY | TIMES | TYPE | WITH | XOR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_se1_, _menhir_s, (se1 : (AltErgoLib.Parsed.lexpr)), _startpos_se1_), _endpos_se2_, _, (se2 : (AltErgoLib.Parsed.lexpr)), _startpos_se2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_se1_ in
            let _endpos = _endpos_se2_ in
            let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_se2_ in
            let _startpos = _startpos_se1_ in
            
# 254 "src/parsers/why_parser.mly"
   ( mk_mod (_startpos, _endpos) se1 se2 )
# 4284 "src/parsers/why_parser.ml"
             in
            _menhir_goto_lexpr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState150 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | AND | AT | AXIOM | BAR | CASESPLIT | COMMA | ELSE | END | EOF | EQUAL | FUNC | GE | GOAL | GT | IN | LE | LEFTARROW | LOGIC | LRARROW | LT | MINUS | NOTEQ | OR | PERCENT | PLUS | POW | POWDOT | PRED | PV | REWRITING | RIGHTARROW | RIGHTBR | RIGHTPAR | RIGHTSQ | SLASH | THEN | THEORY | TIMES | TYPE | WITH | XOR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (AltErgoLib.Parsed.lexpr)), _startpos_e1_), _endpos_e2_, _, (e2 : (AltErgoLib.Parsed.lexpr)), _startpos_e2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_e1_ in
            let _endpos = _endpos_e2_ in
            let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_e2_ in
            let _startpos = _startpos_e1_ in
            
# 310 "src/parsers/why_parser.mly"
   ( mk_bitv_concat (_startpos, _endpos) e1 e2 )
# 4311 "src/parsers/why_parser.ml"
             in
            _menhir_goto_lexpr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState152 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AXIOM | BAR | CASESPLIT | COMMA | ELSE | END | EOF | FUNC | GOAL | IN | LEFTARROW | LOGIC | LRARROW | PRED | PV | REWRITING | RIGHTARROW | RIGHTBR | RIGHTPAR | RIGHTSQ | THEN | THEORY | TYPE | WITH | XOR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_se1_, _menhir_s, (se1 : (AltErgoLib.Parsed.lexpr)), _startpos_se1_), _endpos_se2_, _, (se2 : (AltErgoLib.Parsed.lexpr)), _startpos_se2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_se1_ in
            let _endpos = _endpos_se2_ in
            let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_se2_ in
            let _startpos = _startpos_se1_ in
            
# 266 "src/parsers/why_parser.mly"
   ( mk_or (_startpos, _endpos) se1 se2 )
# 4370 "src/parsers/why_parser.ml"
             in
            _menhir_goto_lexpr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState154 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AND | AXIOM | BAR | CASESPLIT | COMMA | ELSE | END | EOF | EQUAL | FUNC | GE | GOAL | GT | IN | LE | LEFTARROW | LOGIC | LRARROW | LT | NOTEQ | OR | PRED | PV | REWRITING | RIGHTARROW | RIGHTBR | RIGHTPAR | RIGHTSQ | THEN | THEORY | TYPE | WITH | XOR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_se1_, _menhir_s, (se1 : (AltErgoLib.Parsed.lexpr)), _startpos_se1_), _endpos_se2_, _, (se2 : (AltErgoLib.Parsed.lexpr)), _startpos_se2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_se1_ in
            let _endpos = _endpos_se2_ in
            let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_se2_ in
            let _startpos = _startpos_se1_ in
            
# 293 "src/parsers/why_parser.mly"
   ( mk_pred_not_eq (_startpos, _endpos) se1 se2 )
# 4413 "src/parsers/why_parser.ml"
             in
            _menhir_goto_lexpr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState156 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AND | AXIOM | BAR | CASESPLIT | COMMA | ELSE | END | EOF | EQUAL | FUNC | GE | GOAL | GT | IN | LE | LEFTARROW | LOGIC | LRARROW | LT | MINUS | NOTEQ | OR | PLUS | PRED | PV | REWRITING | RIGHTARROW | RIGHTBR | RIGHTPAR | RIGHTSQ | THEN | THEORY | TYPE | WITH | XOR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _endpos_se1_, _menhir_s, (se1 : (AltErgoLib.Parsed.lexpr)), _startpos_se1_), _startpos__2_), _endpos_se2_, _, (se2 : (AltErgoLib.Parsed.lexpr)), _startpos_se2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_se1_ in
            let _endpos = _endpos_se2_ in
            let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_se2_ in
            let _startpos = _startpos_se1_ in
            
# 245 "src/parsers/why_parser.mly"
   ( mk_sub (_startpos, _endpos) se1 se2 )
# 4452 "src/parsers/why_parser.ml"
             in
            _menhir_goto_lexpr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState158 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AND | AXIOM | BAR | CASESPLIT | COMMA | ELSE | END | EOF | EQUAL | FUNC | GE | GOAL | GT | IN | LE | LEFTARROW | LOGIC | LRARROW | LT | NOTEQ | OR | PRED | PV | REWRITING | RIGHTARROW | RIGHTBR | RIGHTPAR | RIGHTSQ | THEN | THEORY | TYPE | WITH | XOR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_se1_, _menhir_s, (se1 : (AltErgoLib.Parsed.lexpr)), _startpos_se1_), _endpos_se2_, _, (se2 : (AltErgoLib.Parsed.lexpr)), _startpos_se2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_se1_ in
            let _endpos = _endpos_se2_ in
            let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_se2_ in
            let _startpos = _startpos_se1_ in
            
# 278 "src/parsers/why_parser.mly"
   ( mk_pred_lt (_startpos, _endpos) se1 se2 )
# 4495 "src/parsers/why_parser.ml"
             in
            _menhir_goto_lexpr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState160 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AND | AXIOM | BAR | CASESPLIT | COMMA | ELSE | END | EOF | EQUAL | FUNC | GE | GOAL | GT | IN | LE | LEFTARROW | LOGIC | LRARROW | LT | NOTEQ | OR | PRED | PV | REWRITING | RIGHTARROW | RIGHTBR | RIGHTPAR | RIGHTSQ | THEN | THEORY | TYPE | WITH | XOR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_se1_, _menhir_s, (se1 : (AltErgoLib.Parsed.lexpr)), _startpos_se1_), _endpos_se2_, _, (se2 : (AltErgoLib.Parsed.lexpr)), _startpos_se2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_se1_ in
            let _endpos = _endpos_se2_ in
            let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_se2_ in
            let _startpos = _startpos_se1_ in
            
# 281 "src/parsers/why_parser.mly"
   ( mk_pred_le (_startpos, _endpos) se1 se2 )
# 4538 "src/parsers/why_parser.ml"
             in
            _menhir_goto_lexpr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState162 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AND | AXIOM | BAR | CASESPLIT | COMMA | ELSE | END | EOF | EQUAL | FUNC | GE | GOAL | GT | IN | LE | LEFTARROW | LOGIC | LRARROW | LT | NOTEQ | OR | PRED | PV | REWRITING | RIGHTARROW | RIGHTBR | RIGHTPAR | RIGHTSQ | THEN | THEORY | TYPE | WITH | XOR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_se1_, _menhir_s, (se1 : (AltErgoLib.Parsed.lexpr)), _startpos_se1_), _endpos_se2_, _, (se2 : (AltErgoLib.Parsed.lexpr)), _startpos_se2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_se1_ in
            let _endpos = _endpos_se2_ in
            let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_se2_ in
            let _startpos = _startpos_se1_ in
            
# 284 "src/parsers/why_parser.mly"
   ( mk_pred_gt (_startpos, _endpos) se1 se2 )
# 4581 "src/parsers/why_parser.ml"
             in
            _menhir_goto_lexpr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState164 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AND | AXIOM | BAR | CASESPLIT | COMMA | ELSE | END | EOF | EQUAL | FUNC | GE | GOAL | GT | IN | LE | LEFTARROW | LOGIC | LRARROW | LT | NOTEQ | OR | PRED | PV | REWRITING | RIGHTARROW | RIGHTBR | RIGHTPAR | RIGHTSQ | THEN | THEORY | TYPE | WITH | XOR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_se1_, _menhir_s, (se1 : (AltErgoLib.Parsed.lexpr)), _startpos_se1_), _endpos_se2_, _, (se2 : (AltErgoLib.Parsed.lexpr)), _startpos_se2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_se1_ in
            let _endpos = _endpos_se2_ in
            let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_se2_ in
            let _startpos = _startpos_se1_ in
            
# 287 "src/parsers/why_parser.mly"
   ( mk_pred_ge (_startpos, _endpos) se1 se2 )
# 4624 "src/parsers/why_parser.ml"
             in
            _menhir_goto_lexpr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState166 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AND | AXIOM | BAR | CASESPLIT | COMMA | ELSE | END | EOF | EQUAL | FUNC | GE | GOAL | GT | IN | LE | LEFTARROW | LOGIC | LRARROW | LT | NOTEQ | OR | PRED | PV | REWRITING | RIGHTARROW | RIGHTBR | RIGHTPAR | RIGHTSQ | THEN | THEORY | TYPE | WITH | XOR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_se1_, _menhir_s, (se1 : (AltErgoLib.Parsed.lexpr)), _startpos_se1_), _endpos_se2_, _, (se2 : (AltErgoLib.Parsed.lexpr)), _startpos_se2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_se1_ in
            let _endpos = _endpos_se2_ in
            let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_se2_ in
            let _startpos = _startpos_se1_ in
            
# 290 "src/parsers/why_parser.mly"
   ( mk_pred_eq (_startpos, _endpos) se1 se2 )
# 4667 "src/parsers/why_parser.ml"
             in
            _menhir_goto_lexpr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState168 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AXIOM | BAR | CASESPLIT | COMMA | ELSE | END | EOF | FUNC | GOAL | IN | LEFTARROW | LOGIC | LRARROW | OR | PRED | PV | REWRITING | RIGHTARROW | RIGHTBR | RIGHTPAR | RIGHTSQ | THEN | THEORY | TYPE | WITH | XOR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _endpos_se1_, _menhir_s, (se1 : (AltErgoLib.Parsed.lexpr)), _startpos_se1_), _startpos__2_), _endpos_se2_, _, (se2 : (AltErgoLib.Parsed.lexpr)), _startpos_se2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_se1_ in
            let _endpos = _endpos_se2_ in
            let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_se2_ in
            let _startpos = _startpos_se1_ in
            
# 263 "src/parsers/why_parser.mly"
   ( mk_and (_startpos, _endpos) se1 se2 )
# 4724 "src/parsers/why_parser.ml"
             in
            _menhir_goto_lexpr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState170 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LRARROW ->
            _menhir_run170 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTARROW ->
            _menhir_run140 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | XOR ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AXIOM | BAR | CASESPLIT | COMMA | ELSE | END | EOF | FUNC | GOAL | IN | LEFTARROW | LOGIC | PRED | PV | REWRITING | RIGHTBR | RIGHTPAR | RIGHTSQ | THEN | THEORY | TYPE | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_se1_, _menhir_s, (se1 : (AltErgoLib.Parsed.lexpr)), _startpos_se1_), _endpos_se2_, _, (se2 : (AltErgoLib.Parsed.lexpr)), _startpos_se2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_se1_ in
            let _endpos = _endpos_se2_ in
            let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_se2_ in
            let _startpos = _startpos_se1_ in
            
# 272 "src/parsers/why_parser.mly"
   ( mk_iff (_startpos, _endpos) se1 se2 )
# 4789 "src/parsers/why_parser.ml"
             in
            _menhir_goto_lexpr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState175 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LRARROW ->
            _menhir_run170 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTARROW ->
            _menhir_run140 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | XOR ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | COMMA | RIGHTSQ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (AltErgoLib.Parsed.lexpr)), _startpos_e1_), _endpos_e2_, _, (e2 : (AltErgoLib.Parsed.lexpr)), _startpos_e2_) = _menhir_stack in
            let _2 = () in
            let _v : (AltErgoLib.Parsed.lexpr * AltErgoLib.Parsed.lexpr) = 
# 436 "src/parsers/why_parser.mly"
                                   ( e1, e2 )
# 4850 "src/parsers/why_parser.ml"
             in
            let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | COMMA ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | CHECK ->
                    _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState180 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | CUT ->
                    _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState180 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | DISTINCT ->
                    _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState180 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | EXISTS ->
                    _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState180 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | FALSE ->
                    _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState180 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | FORALL ->
                    _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState180 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | ID _v ->
                    _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState180 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | IF ->
                    _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState180 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | INTEGER _v ->
                    _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState180 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LEFTBR ->
                    _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState180 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LEFTPAR ->
                    _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState180 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LEFTSQ ->
                    _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState180 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LET ->
                    _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState180 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | MATCH ->
                    _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState180 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | MINUS ->
                    _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState180 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | NOT ->
                    _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState180 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | NUM _v ->
                    _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState180 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | STRING _v ->
                    _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState180 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TRUE ->
                    _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState180 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | VOID ->
                    _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState180 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState180)
            | RIGHTSQ ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, (assign : (AltErgoLib.Parsed.lexpr * AltErgoLib.Parsed.lexpr))) = _menhir_stack in
                let _v : ((AltErgoLib.Parsed.lexpr * AltErgoLib.Parsed.lexpr) list) = 
# 431 "src/parsers/why_parser.mly"
   ( [assign] )
# 4912 "src/parsers/why_parser.ml"
                 in
                _menhir_goto_array_assignements _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState180 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LEFTARROW ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | LRARROW ->
            _menhir_run170 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTARROW ->
            _menhir_run140 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | XOR ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState113 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos_e_, _, (e : (AltErgoLib.Parsed.lexpr)), _startpos_e_) = _menhir_stack in
        let _1 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_e_ in
        let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_e_ in
        let _startpos = _startpos__1_ in
        
# 349 "src/parsers/why_parser.mly"
   ( mk_check (_startpos, _endpos) e )
# 4992 "src/parsers/why_parser.ml"
         in
        _menhir_goto_lexpr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | MenhirState112 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos_e_, _, (e : (AltErgoLib.Parsed.lexpr)), _startpos_e_) = _menhir_stack in
        let _1 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_e_ in
        let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_e_ in
        let _startpos = _startpos__1_ in
        
# 352 "src/parsers/why_parser.mly"
   ( mk_cut (_startpos, _endpos) e )
# 5007 "src/parsers/why_parser.ml"
         in
        _menhir_goto_lexpr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | MenhirState111 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | COMMA ->
            _menhir_run192 _menhir_env (Obj.magic _menhir_stack)
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LRARROW ->
            _menhir_run170 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTARROW ->
            _menhir_run140 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | XOR ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState192 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | COMMA ->
            _menhir_run192 _menhir_env (Obj.magic _menhir_stack)
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LRARROW ->
            _menhir_run170 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTARROW ->
            _menhir_run140 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | XOR ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTPAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (AltErgoLib.Parsed.lexpr)), _startpos_e1_), _endpos_e2_, _, (e2 : (AltErgoLib.Parsed.lexpr)), _startpos_e2_) = _menhir_stack in
            let _2 = () in
            let _v : (AltErgoLib.Parsed.lexpr list) = 
# 499 "src/parsers/why_parser.mly"
                                              ( [e1; e2] )
# 5117 "src/parsers/why_parser.ml"
             in
            _menhir_goto_list2_lexpr_sep_comma _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState109 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | CHECK ->
                _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | CUT ->
                _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DISTINCT ->
                _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | EXISTS ->
                _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FALSE ->
                _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FORALL ->
                _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState197 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | IF ->
                _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | INTEGER _v ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState197 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTBR ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTPAR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTSQ ->
                _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LET ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MATCH ->
                _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MINUS ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NOT ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NUM _v ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState197 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | STRING _v ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState197 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TRUE ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | VOID ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | RIGHTBR ->
                _menhir_reduce76 _menhir_env (Obj.magic _menhir_stack) MenhirState197
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState197)
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LRARROW ->
            _menhir_run170 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTARROW ->
            _menhir_run140 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTBR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos_filt_, _, (filt : (AltErgoLib.Parsed.lexpr)), _startpos_filt_) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (AltErgoLib.Parsed.lexpr list) = 
# 447 "src/parsers/why_parser.mly"
   ( [filt] )
# 5228 "src/parsers/why_parser.ml"
             in
            _menhir_goto_filters _menhir_env _menhir_stack _menhir_s _v
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | XOR ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState201 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LRARROW ->
            _menhir_run170 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTARROW ->
            _menhir_run140 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | XOR ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AXIOM | BAR | CASESPLIT | COMMA | ELSE | END | EOF | FUNC | GOAL | IN | LEFTARROW | LOGIC | PRED | PV | REWRITING | RIGHTBR | RIGHTPAR | RIGHTSQ | THEN | THEORY | TYPE | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((((_menhir_stack, _menhir_s, _startpos__1_), _, (quant_vars : (((string * string) list * AltErgoLib.Parsed.ppure_type) list))), _, (triggers : ((AltErgoLib.Parsed.lexpr list * bool) list))), _, (filters : (AltErgoLib.Parsed.lexpr list))), _endpos_body_, _, (body : (AltErgoLib.Parsed.lexpr)), _startpos_body_) = _menhir_stack in
            let _5 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos_body_ in
            let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_body_ in
            let _startpos = _startpos__1_ in
            
# 333 "src/parsers/why_parser.mly"
   (
     let vs_ty =
       List.map (fun (vs, ty) ->
         List.map (fun (v, name) -> v, name, ty) vs) quant_vars
     in
     let vs_ty = List.flatten vs_ty in
     mk_exists (_startpos, _endpos) vs_ty triggers filters body
   )
# 5307 "src/parsers/why_parser.ml"
             in
            _menhir_goto_lexpr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState352 | MenhirState105 | MenhirState204 | MenhirState208 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | IN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LEFTSQ ->
                _menhir_run213 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState211 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | RIGHTSQ ->
                _menhir_run212 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState211
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState211)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LRARROW ->
            _menhir_run170 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTARROW ->
            _menhir_run140 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | XOR ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | BAR | COMMA | EOF | RIGHTSQ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _endpos_e_, _menhir_s, (e : (AltErgoLib.Parsed.lexpr)), _startpos_e_) = _menhir_stack in
            let _v : (AltErgoLib.Parsed.lexpr) = 
# 478 "src/parsers/why_parser.mly"
   ( e )
# 5380 "src/parsers/why_parser.ml"
             in
            _menhir_goto_lexpr_or_dom _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState228 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LRARROW ->
            _menhir_run170 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTARROW ->
            _menhir_run140 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | XOR ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | BAR | COMMA | EOF | RIGHTSQ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_id_, _menhir_s, (id : (string)), _startpos_id_), _endpos_e_, _, (e : (AltErgoLib.Parsed.lexpr)), _startpos_e_) = _menhir_stack in
            let _2 = () in
            let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_e_ in
            let _startpos = _startpos_id_ in
            
# 482 "src/parsers/why_parser.mly"
   ( mk_maps_to (_startpos, _endpos) id e )
# 5443 "src/parsers/why_parser.ml"
             in
            _menhir_goto_lexpr_or_dom _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState234 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LRARROW ->
            _menhir_run170 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTARROW ->
            _menhir_run140 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | XOR ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AXIOM | BAR | CASESPLIT | COMMA | ELSE | END | EOF | FUNC | GOAL | IN | LEFTARROW | LOGIC | PRED | PV | REWRITING | RIGHTBR | RIGHTPAR | RIGHTSQ | THEN | THEORY | TYPE | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((((_menhir_stack, _menhir_s, _startpos__1_), _, (quant_vars : (((string * string) list * AltErgoLib.Parsed.ppure_type) list))), _, (triggers : ((AltErgoLib.Parsed.lexpr list * bool) list))), _, (filters : (AltErgoLib.Parsed.lexpr list))), _endpos_body_, _, (body : (AltErgoLib.Parsed.lexpr)), _startpos_body_) = _menhir_stack in
            let _5 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos_body_ in
            let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_body_ in
            let _startpos = _startpos__1_ in
            
# 322 "src/parsers/why_parser.mly"
   (
     let vs_ty =
       List.map (fun (vs, ty) ->
         List.map (fun (v, name) -> v, name, ty) vs) quant_vars
     in
     let vs_ty = List.flatten vs_ty in
     mk_forall (_startpos, _endpos) vs_ty triggers filters body
   )
# 5516 "src/parsers/why_parser.ml"
             in
            _menhir_goto_lexpr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState91 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LRARROW ->
            _menhir_run170 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTARROW ->
            _menhir_run140 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | CHECK ->
                _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState237 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | CUT ->
                _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState237 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DISTINCT ->
                _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState237 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | EXISTS ->
                _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState237 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FALSE ->
                _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState237 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FORALL ->
                _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState237 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState237 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | IF ->
                _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState237 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | INTEGER _v ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState237 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTBR ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState237 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTPAR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState237 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTSQ ->
                _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState237 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LET ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState237 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MATCH ->
                _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState237 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MINUS ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState237 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NOT ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState237 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NUM _v ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState237 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | STRING _v ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState237 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TRUE ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState237 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | VOID ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState237 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState237)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | XOR ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState237 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | ELSE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | CHECK ->
                _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState239 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | CUT ->
                _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState239 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DISTINCT ->
                _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState239 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | EXISTS ->
                _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState239 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FALSE ->
                _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState239 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FORALL ->
                _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState239 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState239 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | IF ->
                _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState239 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | INTEGER _v ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState239 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTBR ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState239 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTPAR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState239 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTSQ ->
                _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState239 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LET ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState239 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MATCH ->
                _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState239 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MINUS ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState239 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NOT ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState239 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NUM _v ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState239 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | STRING _v ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState239 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TRUE ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState239 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | VOID ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState239 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState239)
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LRARROW ->
            _menhir_run170 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTARROW ->
            _menhir_run140 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | XOR ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState239 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AND | AXIOM | BAR | CASESPLIT | COMMA | ELSE | END | EOF | FUNC | GOAL | IN | LEFTARROW | LOGIC | LRARROW | OR | PRED | PV | REWRITING | RIGHTARROW | RIGHTBR | RIGHTPAR | RIGHTSQ | THEN | THEORY | TYPE | WITH | XOR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((((_menhir_stack, _menhir_s, _startpos__1_), _endpos_cond_, _, (cond : (AltErgoLib.Parsed.lexpr)), _startpos_cond_), _endpos_br1_, _, (br1 : (AltErgoLib.Parsed.lexpr)), _startpos_br1_), _endpos_br2_, _, (br2 : (AltErgoLib.Parsed.lexpr)), _startpos_br2_) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos_br2_ in
            let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_br2_ in
            let _startpos = _startpos__1_ in
            
# 318 "src/parsers/why_parser.mly"
   ( mk_ite (_startpos, _endpos) cond br1 br2 )
# 5773 "src/parsers/why_parser.ml"
             in
            _menhir_goto_lexpr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState90 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LRARROW ->
            _menhir_run170 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | PV ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState242 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState242)
        | RIGHTARROW ->
            _menhir_run140 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | XOR ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTBR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_id_, _menhir_s, (id : (string)), _startpos_id_), _endpos_e_, _, (e : (AltErgoLib.Parsed.lexpr)), _startpos_e_) = _menhir_stack in
            let _2 = () in
            let _v : ((string * AltErgoLib.Parsed.lexpr) list) = 
# 515 "src/parsers/why_parser.mly"
   ( [id, e] )
# 5847 "src/parsers/why_parser.ml"
             in
            _menhir_goto_list1_label_expr_sep_PV _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState81 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LRARROW ->
            _menhir_run170 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTARROW ->
            _menhir_run140 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTPAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos_e_, _, (e : (AltErgoLib.Parsed.lexpr)), _startpos_e_) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__3_ in
            let _v : (AltErgoLib.Parsed.lexpr) = 
# 416 "src/parsers/why_parser.mly"
   ( e )
# 5909 "src/parsers/why_parser.ml"
             in
            _menhir_goto_simple_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | XOR ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState75 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LRARROW ->
            _menhir_run170 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTARROW ->
            _menhir_run140 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | XOR ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AXIOM | BAR | CASESPLIT | COMMA | ELSE | END | EOF | FUNC | GOAL | IN | LEFTARROW | LOGIC | PRED | PV | REWRITING | RIGHTBR | RIGHTPAR | RIGHTSQ | THEN | THEORY | TYPE | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, _startpos__1_), _, (binders : ((string * AltErgoLib.Parsed.lexpr) list))), _endpos_e2_, _, (e2 : (AltErgoLib.Parsed.lexpr)), _startpos_e2_) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos_e2_ in
            let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_e2_ in
            let _startpos = _startpos__1_ in
            
# 346 "src/parsers/why_parser.mly"
   ( mk_let (_startpos, _endpos) binders e2 )
# 5981 "src/parsers/why_parser.ml"
             in
            _menhir_goto_lexpr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState251 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState253 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState253)
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LRARROW ->
            _menhir_run170 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTARROW ->
            _menhir_run140 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | XOR ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | IN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_binder_, _menhir_s, (binder : (string)), _startpos_binder_), _endpos_e_, _, (e : (AltErgoLib.Parsed.lexpr)), _startpos_e_) = _menhir_stack in
            let _2 = () in
            let _v : ((string * AltErgoLib.Parsed.lexpr) list) = 
# 372 "src/parsers/why_parser.mly"
                                 ( [binder, e] )
# 6053 "src/parsers/why_parser.ml"
             in
            _menhir_goto_let_binders _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState72 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LRARROW ->
            _menhir_run170 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTARROW ->
            _menhir_run140 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BAR ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_s = MenhirState256 in
                let _menhir_stack = (_menhir_stack, _menhir_s) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | ID _v ->
                    _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState257 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState257)
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState256 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState256)
        | XOR ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState259 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LRARROW ->
            _menhir_run170 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTARROW ->
            _menhir_run140 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | XOR ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | BAR | END ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (p : (AltErgoLib.Parsed.pattern))), _endpos_e_, _, (e : (AltErgoLib.Parsed.lexpr)), _startpos_e_) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : ((AltErgoLib.Parsed.pattern * AltErgoLib.Parsed.lexpr) list) = 
# 361 "src/parsers/why_parser.mly"
                                              ( [p, e])
# 6190 "src/parsers/why_parser.ml"
             in
            _menhir_goto_list1_match_cases _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState269 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LRARROW ->
            _menhir_run170 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTARROW ->
            _menhir_run140 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | XOR ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | BAR | END ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (p : (AltErgoLib.Parsed.pattern))), _endpos_e_, _, (e : (AltErgoLib.Parsed.lexpr)), _startpos_e_) = _menhir_stack in
            let _2 = () in
            let _v : ((AltErgoLib.Parsed.pattern * AltErgoLib.Parsed.lexpr) list) = 
# 360 "src/parsers/why_parser.mly"
                                              ( [p, e])
# 6251 "src/parsers/why_parser.ml"
             in
            _menhir_goto_list1_match_cases _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState275 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LRARROW ->
            _menhir_run170 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTARROW ->
            _menhir_run140 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | XOR ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | BAR | END ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, (l : ((AltErgoLib.Parsed.pattern * AltErgoLib.Parsed.lexpr) list))), _, (p : (AltErgoLib.Parsed.pattern))), _endpos_e_, _, (e : (AltErgoLib.Parsed.lexpr)), _startpos_e_) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _v : ((AltErgoLib.Parsed.pattern * AltErgoLib.Parsed.lexpr) list) = 
# 363 "src/parsers/why_parser.mly"
    ( (p,e) :: l )
# 6313 "src/parsers/why_parser.ml"
             in
            _menhir_goto_list1_match_cases _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState71 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos_se_, _, (se : (AltErgoLib.Parsed.lexpr)), _startpos_se_) = _menhir_stack in
        let _1 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_se_ in
        let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_se_ in
        let _startpos = _startpos__1_ in
        
# 299 "src/parsers/why_parser.mly"
   ( mk_minus (_startpos, _endpos) se )
# 6334 "src/parsers/why_parser.ml"
         in
        _menhir_goto_lexpr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | MenhirState70 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos_se_, _, (se : (AltErgoLib.Parsed.lexpr)), _startpos_se_) = _menhir_stack in
        let _1 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_se_ in
        let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_se_ in
        let _startpos = _startpos__1_ in
        
# 296 "src/parsers/why_parser.mly"
   ( mk_not (_startpos, _endpos) se )
# 6349 "src/parsers/why_parser.ml"
         in
        _menhir_goto_lexpr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | MenhirState68 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (name : (
# 42 "src/parsers/why_parser.mly"
       (string)
# 6358 "src/parsers/why_parser.ml"
        )), _startpos_name_), _endpos_e_, _, (e : (AltErgoLib.Parsed.lexpr)), _startpos_e_) = _menhir_stack in
        let _2 = () in
        let _startpos = _startpos_name_ in
        let _endpos = _endpos_e_ in
        let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_e_ in
        let _startpos = _startpos_name_ in
        
# 343 "src/parsers/why_parser.mly"
   ( mk_named (_startpos, _endpos) name e )
# 6368 "src/parsers/why_parser.ml"
         in
        _menhir_goto_lexpr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | MenhirState64 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LRARROW ->
            _menhir_run170 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTARROW ->
            _menhir_run140 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | XOR ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AXIOM | CASESPLIT | END ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, _startpos__1_), _endpos_name_, _, (name : (string)), _startpos_name_), _endpos_body_, _, (body : (AltErgoLib.Parsed.lexpr)), _startpos_body_) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (AltErgoLib.Parsed.decl) = let _endpos = _endpos_body_ in
            let _startpos = _startpos__1_ in
            
# 162 "src/parsers/why_parser.mly"
   ( mk_theory_case_split (_startpos, _endpos) name body )
# 6426 "src/parsers/why_parser.ml"
             in
            _menhir_goto_theory_elt _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState283 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LRARROW ->
            _menhir_run170 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTARROW ->
            _menhir_run140 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | XOR ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AXIOM | CASESPLIT | END ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, _startpos__1_), _endpos_name_, _, (name : (string)), _startpos_name_), _endpos_body_, _, (body : (AltErgoLib.Parsed.lexpr)), _startpos_body_) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (AltErgoLib.Parsed.decl) = let _endpos = _endpos_body_ in
            let _startpos = _startpos__1_ in
            
# 159 "src/parsers/why_parser.mly"
   ( mk_theory_axiom (_startpos, _endpos) name body )
# 6490 "src/parsers/why_parser.ml"
             in
            _menhir_goto_theory_elt _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState294 | MenhirState291 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LRARROW ->
            _menhir_run170 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | PV ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | CHECK ->
                _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState294 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | CUT ->
                _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState294 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DISTINCT ->
                _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState294 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | EXISTS ->
                _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState294 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FALSE ->
                _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState294 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FORALL ->
                _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState294 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState294 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | IF ->
                _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState294 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | INTEGER _v ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState294 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTBR ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState294 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTPAR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState294 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTSQ ->
                _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState294 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LET ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState294 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MATCH ->
                _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState294 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MINUS ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState294 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NOT ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState294 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NUM _v ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState294 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | STRING _v ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState294 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TRUE ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState294 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | VOID ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState294 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | AXIOM | EOF | FUNC | GOAL | LOGIC | PRED | REWRITING | THEORY | TYPE ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _endpos_e_, _menhir_s, (e : (AltErgoLib.Parsed.lexpr)), _startpos_e_), _endpos__2_) = _menhir_stack in
                let _2 = () in
                let _endpos = _endpos__2_ in
                let _v : (AltErgoLib.Parsed.lexpr list) = 
# 461 "src/parsers/why_parser.mly"
                                         ( [e] )
# 6591 "src/parsers/why_parser.ml"
                 in
                _menhir_goto_list1_lexpr_sep_pv _menhir_env _menhir_stack _endpos _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState294)
        | RIGHTARROW ->
            _menhir_run140 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | XOR ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AXIOM | EOF | FUNC | GOAL | LOGIC | PRED | REWRITING | THEORY | TYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _endpos_e_, _menhir_s, (e : (AltErgoLib.Parsed.lexpr)), _startpos_e_) = _menhir_stack in
            let _endpos = _endpos_e_ in
            let _v : (AltErgoLib.Parsed.lexpr list) = 
# 460 "src/parsers/why_parser.mly"
                                         ( [e] )
# 6613 "src/parsers/why_parser.ml"
             in
            _menhir_goto_list1_lexpr_sep_pv _menhir_env _menhir_stack _endpos _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState308 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LRARROW ->
            _menhir_run170 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTARROW ->
            _menhir_run140 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | XOR ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AXIOM | EOF | FUNC | GOAL | LOGIC | PRED | REWRITING | THEORY | TYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((((((_menhir_stack, _menhir_s, _startpos__1_), _, (app : (string * string))), _startpos__3_), _, (args : ((AltErgoLib.Loc.t * string * AltErgoLib.Parsed.ppure_type) list))), _endpos__5_), _endpos_body_, _, (body : (AltErgoLib.Parsed.lexpr)), _startpos_body_) = _menhir_stack in
            let _6 = () in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : (AltErgoLib.Parsed.decl) = let _endpos = _endpos_body_ in
            let _startpos = _startpos__1_ in
            
# 142 "src/parsers/why_parser.mly"
   ( mk_non_ground_predicate_def (_startpos, _endpos) app args body )
# 6679 "src/parsers/why_parser.ml"
             in
            _menhir_goto_decl _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState310 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LRARROW ->
            _menhir_run170 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTARROW ->
            _menhir_run140 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | XOR ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AXIOM | EOF | FUNC | GOAL | LOGIC | PRED | REWRITING | THEORY | TYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, _startpos__1_), _, (app : (string * string))), _endpos_body_, _, (body : (AltErgoLib.Parsed.lexpr)), _startpos_body_) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (AltErgoLib.Parsed.decl) = let _endpos = _endpos_body_ in
            let _startpos = _startpos__1_ in
            
# 138 "src/parsers/why_parser.mly"
   ( mk_ground_predicate_def (_startpos, _endpos) app body )
# 6743 "src/parsers/why_parser.ml"
             in
            _menhir_goto_decl _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState327 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LRARROW ->
            _menhir_run170 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTARROW ->
            _menhir_run140 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | XOR ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AXIOM | EOF | FUNC | GOAL | LOGIC | PRED | REWRITING | THEORY | TYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, _startpos__1_), _endpos_name_, _, (name : (string)), _startpos_name_), _endpos_body_, _, (body : (AltErgoLib.Parsed.lexpr)), _startpos_body_) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (AltErgoLib.Parsed.decl) = let _endpos = _endpos_body_ in
            let _startpos = _startpos__1_ in
            
# 151 "src/parsers/why_parser.mly"
   ( mk_goal (_startpos, _endpos) name body )
# 6807 "src/parsers/why_parser.ml"
             in
            _menhir_goto_decl _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState336 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LRARROW ->
            _menhir_run170 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTARROW ->
            _menhir_run140 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | XOR ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AXIOM | EOF | FUNC | GOAL | LOGIC | PRED | REWRITING | THEORY | TYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((((((((_menhir_stack, _menhir_s, _startpos__1_), _, (app : (string * string))), _startpos__3_), _, (args : ((AltErgoLib.Loc.t * string * AltErgoLib.Parsed.ppure_type) list))), _endpos__5_), _endpos_ret_ty_, _, (ret_ty : (AltErgoLib.Parsed.ppure_type))), _), _endpos_body_, _, (body : (AltErgoLib.Parsed.lexpr)), _startpos_body_) = _menhir_stack in
            let _8 = () in
            let _6 = () in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : (AltErgoLib.Parsed.decl) = let _endpos = _endpos_body_ in
            let _startpos = _startpos__1_ in
            
# 135 "src/parsers/why_parser.mly"
   ( mk_function_def (_startpos, _endpos) app args ret_ty body )
# 6874 "src/parsers/why_parser.ml"
             in
            _menhir_goto_decl _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState341 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LRARROW ->
            _menhir_run170 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTARROW ->
            _menhir_run140 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | XOR ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AXIOM | EOF | FUNC | GOAL | LOGIC | PRED | REWRITING | THEORY | TYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, _startpos__1_), _endpos_name_, _, (name : (string)), _startpos_name_), _endpos_body_, _, (body : (AltErgoLib.Parsed.lexpr)), _startpos_body_) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (AltErgoLib.Parsed.decl) = let _endpos = _endpos_body_ in
            let _startpos = _startpos__1_ in
            
# 145 "src/parsers/why_parser.mly"
   ( mk_generic_axiom (_startpos, _endpos) name body )
# 6938 "src/parsers/why_parser.ml"
             in
            _menhir_goto_decl _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState348 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack)
        | EOF ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _endpos_e_, _menhir_s, (e : (AltErgoLib.Parsed.lexpr)), _startpos_e_) = _menhir_stack in
            let _2 = () in
            let _v : (
# 79 "src/parsers/why_parser.mly"
      (AltErgoLib.Parsed.lexpr)
# 6964 "src/parsers/why_parser.ml"
            ) = 
# 94 "src/parsers/why_parser.mly"
                ( e )
# 6968 "src/parsers/why_parser.ml"
             in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_1 : (
# 79 "src/parsers/why_parser.mly"
      (AltErgoLib.Parsed.lexpr)
# 6975 "src/parsers/why_parser.ml"
            )) = _v in
            Obj.magic _1
        | EQUAL ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack)
        | HAT ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack)
        | LE ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
        | LRARROW ->
            _menhir_run170 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run158 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run156 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTEQ ->
            _menhir_run154 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack)
        | POWDOT ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | RIGHTARROW ->
            _menhir_run140 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | TIMES ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | XOR ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_list1_string_sep_comma : _menhir_env -> 'ttv_tail -> _menhir_state -> (string list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState262 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RIGHTPAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let (((_menhir_stack, _endpos_app_, _menhir_s, (app : (string)), _startpos_app_), _startpos__2_), _, (args : (string list))) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _v : (AltErgoLib.Parsed.pattern) = let _endpos = _endpos__4_ in
            let _startpos = _startpos_app_ in
            
# 368 "src/parsers/why_parser.mly"
   ( mk_pattern (_startpos, _endpos) app args )
# 7046 "src/parsers/why_parser.ml"
             in
            _menhir_goto_simple_pattern _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState266 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _endpos_id_, _menhir_s, (id : (string)), _startpos_id_), _, (l : (string list))) = _menhir_stack in
        let _2 = () in
        let _v : (string list) = 
# 551 "src/parsers/why_parser.mly"
                                              ( id :: l  )
# 7063 "src/parsers/why_parser.ml"
         in
        _menhir_goto_list1_string_sep_comma _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_simple_pattern : _menhir_env -> 'ttv_tail -> _menhir_state -> (AltErgoLib.Parsed.pattern) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState257 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RIGHTARROW ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | CHECK ->
                _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState259 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | CUT ->
                _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState259 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DISTINCT ->
                _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState259 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | EXISTS ->
                _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState259 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FALSE ->
                _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState259 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FORALL ->
                _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState259 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState259 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | IF ->
                _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState259 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | INTEGER _v ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState259 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTBR ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState259 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTPAR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState259 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTSQ ->
                _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState259 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LET ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState259 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MATCH ->
                _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState259 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MINUS ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState259 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NOT ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState259 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NUM _v ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState259 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | STRING _v ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState259 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TRUE ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState259 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | VOID ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState259 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState259)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState256 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RIGHTARROW ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | CHECK ->
                _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState269 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | CUT ->
                _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState269 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DISTINCT ->
                _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState269 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | EXISTS ->
                _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState269 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FALSE ->
                _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState269 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FORALL ->
                _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState269 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState269 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | IF ->
                _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState269 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | INTEGER _v ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState269 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTBR ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState269 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTPAR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState269 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTSQ ->
                _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState269 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LET ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState269 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MATCH ->
                _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState269 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MINUS ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState269 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NOT ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState269 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NUM _v ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState269 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | STRING _v ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState269 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TRUE ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState269 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | VOID ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState269 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState269)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState273 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RIGHTARROW ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | CHECK ->
                _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState275 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | CUT ->
                _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState275 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DISTINCT ->
                _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState275 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | EXISTS ->
                _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState275 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FALSE ->
                _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState275 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FORALL ->
                _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState275 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState275 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | IF ->
                _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState275 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | INTEGER _v ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState275 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTBR ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState275 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTPAR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState275 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTSQ ->
                _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState275 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LET ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState275 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MATCH ->
                _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState275 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MINUS ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState275 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NOT ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState275 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NUM _v ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState275 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | STRING _v ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState275 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TRUE ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState275 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | VOID ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState275 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState275)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_reduce139 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (string) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _endpos_var_, _menhir_s, (var : (string)), _startpos_var_) = _menhir_stack in
    let _startpos = _startpos_var_ in
    let _endpos = _endpos_var_ in
    let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_var_ in
    let _startpos = _startpos_var_ in
    
# 381 "src/parsers/why_parser.mly"
              ( mk_var (_startpos, _endpos) var )
# 7266 "src/parsers/why_parser.ml"
     in
    _menhir_goto_simple_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run133 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (string) * Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _startpos ->
    let _menhir_stack = (_menhir_stack, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHECK ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CUT ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DISTINCT ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXISTS ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState133 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FORALL ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState133 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState133 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTSQ ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState133 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LET ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState133 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRING _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState133 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState133 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | RIGHTPAR ->
        _menhir_reduce76 _menhir_env (Obj.magic _menhir_stack) MenhirState133
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState133

and _menhir_run90 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (string) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHECK ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState90 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CUT ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState90 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DISTINCT ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState90 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXISTS ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState90 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState90 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FORALL ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState90 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState90 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState90 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState90 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState90 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState90 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTSQ ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState90 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LET ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState90 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState90 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState90 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState90 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState90 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRING _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState90 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState90 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState90 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState90

and _menhir_reduce157 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (AltErgoLib.Parsed.decl list) = 
# 154 "src/parsers/why_parser.mly"
         ( [] )
# 7378 "src/parsers/why_parser.ml"
     in
    _menhir_goto_theory_elts _menhir_env _menhir_stack _menhir_s _v

and _menhir_run62 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState62 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState62

and _menhir_run281 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState281 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState281

and _menhir_goto_algebraic_args : _menhir_env -> 'ttv_tail -> Lexing.position -> ((string * AltErgoLib.Parsed.ppure_type) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _v ->
    let _menhir_stack = (_menhir_stack, _endpos, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BAR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ID _v ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState53 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState53)
    | AND | AXIOM | EOF | FUNC | GOAL | LOGIC | PRED | REWRITING | THEORY | TYPE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _endpos_cons_, _menhir_s, (cons : (string)), _startpos_cons_), _endpos__2_, (_2 : ((string * AltErgoLib.Parsed.ppure_type) list))) = _menhir_stack in
        let _endpos = _endpos__2_ in
        let _v : ((string * (string * AltErgoLib.Parsed.ppure_type) list) list) = 
# 221 "src/parsers/why_parser.mly"
                              ( [cons, _2] )
# 7433 "src/parsers/why_parser.ml"
         in
        _menhir_goto_list1_constructors_sep_bar _menhir_env _menhir_stack _endpos _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run22 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _1 = () in
    let _endpos = _endpos__1_ in
    let _v : (AltErgoLib.Parsed.ppure_type) = 
# 173 "src/parsers/why_parser.mly"
       ( unit_type )
# 7453 "src/parsers/why_parser.ml"
     in
    _menhir_goto_primitive_type _menhir_env _menhir_stack _endpos _menhir_s _v

and _menhir_run23 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _1 = () in
    let _endpos = _endpos__1_ in
    let _v : (AltErgoLib.Parsed.ppure_type) = 
# 172 "src/parsers/why_parser.mly"
       ( real_type )
# 7467 "src/parsers/why_parser.ml"
     in
    _menhir_goto_primitive_type _menhir_env _menhir_stack _endpos _menhir_s _v

and _menhir_run24 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BITV ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | BOOL ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState24
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState24 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INT ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState24
    | LEFTPAR ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState24 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | QUOTE ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState24 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | REAL ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState24
    | UNIT ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState24
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState24

and _menhir_run25 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _1 = () in
    let _endpos = _endpos__1_ in
    let _v : (AltErgoLib.Parsed.ppure_type) = 
# 170 "src/parsers/why_parser.mly"
       ( int_type )
# 7508 "src/parsers/why_parser.ml"
     in
    _menhir_goto_primitive_type _menhir_env _menhir_stack _endpos _menhir_s _v

and _menhir_run26 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _1 = () in
    let _endpos = _endpos__1_ in
    let _v : (AltErgoLib.Parsed.ppure_type) = 
# 171 "src/parsers/why_parser.mly"
       ( bool_type )
# 7522 "src/parsers/why_parser.ml"
     in
    _menhir_goto_primitive_type _menhir_env _menhir_stack _endpos _menhir_s _v

and _menhir_run27 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LEFTSQ ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _endpos, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | INTEGER _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | RIGHTSQ ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos__4_ = _endpos in
                let (((_menhir_stack, _menhir_s), _endpos__2_, _startpos__2_), _endpos_sz_, (sz : (
# 40 "src/parsers/why_parser.mly"
       (string)
# 7557 "src/parsers/why_parser.ml"
                )), _startpos_sz_) = _menhir_stack in
                let _4 = () in
                let _2 = () in
                let _1 = () in
                let _endpos = _endpos__4_ in
                let _v : (AltErgoLib.Parsed.ppure_type) = 
# 174 "src/parsers/why_parser.mly"
                                   ( mk_bitv_type sz )
# 7566 "src/parsers/why_parser.ml"
                 in
                _menhir_goto_primitive_type _menhir_env _menhir_stack _endpos _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (((_menhir_stack, _menhir_s), _, _), _, _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_decl : _menhir_env -> 'ttv_tail -> _menhir_state -> (AltErgoLib.Parsed.decl) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AXIOM ->
        _menhir_run339 _menhir_env (Obj.magic _menhir_stack) MenhirState346 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FUNC ->
        _menhir_run329 _menhir_env (Obj.magic _menhir_stack) MenhirState346 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | GOAL ->
        _menhir_run325 _menhir_env (Obj.magic _menhir_stack) MenhirState346 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LOGIC ->
        _menhir_run312 _menhir_env (Obj.magic _menhir_stack) MenhirState346 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | PRED ->
        _menhir_run296 _menhir_env (Obj.magic _menhir_stack) MenhirState346 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | REWRITING ->
        _menhir_run289 _menhir_env (Obj.magic _menhir_stack) MenhirState346 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | THEORY ->
        _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState346 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TYPE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState346 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EOF ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (decl : (AltErgoLib.Parsed.decl))) = _menhir_stack in
        let _v : (AltErgoLib.Parsed.file) = 
# 97 "src/parsers/why_parser.mly"
              ( [decl] )
# 7617 "src/parsers/why_parser.ml"
         in
        _menhir_goto_list1_decl _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState346

and _menhir_run14 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState14 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState14

and _menhir_fail : unit -> 'a =
  fun () ->
    Printf.fprintf stderr "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

and _menhir_goto_type_vars : _menhir_env -> 'ttv_tail -> _menhir_state -> (string list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState1 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ID _v ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState11 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState11)
    | MenhirState43 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ID _v ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState44 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState44)
    | _ ->
        _menhir_fail ()

and _menhir_goto_primitive_type : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (AltErgoLib.Parsed.ppure_type) -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState33 | MenhirState24 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | ID _v ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState32 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | RIGHTARROW | RIGHTPAR ->
            _menhir_reduce106 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState32)
    | MenhirState21 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ID _v ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState40 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | PV | RIGHTBR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_id_, _menhir_s, (id : (string)), _startpos_id_), _endpos_ty_, _, (ty : (AltErgoLib.Parsed.ppure_type))) = _menhir_stack in
            let _2 = () in
            let _v : (string * AltErgoLib.Parsed.ppure_type) = 
# 510 "src/parsers/why_parser.mly"
                                       ( id, ty )
# 7705 "src/parsers/why_parser.ml"
             in
            let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | PV ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let _menhir_stack = (_menhir_stack, _endpos) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | ID _v ->
                    _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState18 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState18)
            | RIGHTBR ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, (label_typed : (string * AltErgoLib.Parsed.ppure_type))) = _menhir_stack in
                let _v : ((string * AltErgoLib.Parsed.ppure_type) list) = 
# 506 "src/parsers/why_parser.mly"
                                                        ( [label_typed] )
# 7731 "src/parsers/why_parser.ml"
                 in
                _menhir_goto_list1_label_sep_PV _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState40)
    | MenhirState101 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ID _v ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState102 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | COMMA | DOT | LEFTBR | LEFTSQ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (binders : ((string * string) list))), _endpos_ty_, _, (ty : (AltErgoLib.Parsed.ppure_type))) = _menhir_stack in
            let _2 = () in
            let _v : ((string * string) list * AltErgoLib.Parsed.ppure_type) = 
# 536 "src/parsers/why_parser.mly"
    ( binders, ty )
# 7758 "src/parsers/why_parser.ml"
             in
            let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | COMMA ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | ID _v ->
                    _menhir_run93 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState99 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState99)
            | DOT | LEFTBR | LEFTSQ ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, (binders : ((string * string) list * AltErgoLib.Parsed.ppure_type))) = _menhir_stack in
                let _v : (((string * string) list * AltErgoLib.Parsed.ppure_type) list) = 
# 540 "src/parsers/why_parser.mly"
   ( [binders] )
# 7782 "src/parsers/why_parser.ml"
                 in
                _menhir_goto_list1_multi_logic_binder _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState102)
    | MenhirState185 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ID _v ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState186 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AND | AT | AXIOM | BAR | CASESPLIT | COLON | COMMA | DOT | ELSE | END | EOF | EQUAL | FUNC | GE | GOAL | GT | HAT | IN | LE | LEFTARROW | LEFTSQ | LOGIC | LRARROW | LT | MINUS | NOTEQ | OR | PERCENT | PLUS | POW | POWDOT | PRED | PV | QM | QM_ID _ | REWRITING | RIGHTARROW | RIGHTBR | RIGHTPAR | RIGHTSQ | SHARP | SLASH | THEN | THEORY | TIMES | TYPE | WITH | XOR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_se_, _menhir_s, (se : (AltErgoLib.Parsed.lexpr)), _startpos_se_), _endpos_ty_, _, (ty : (AltErgoLib.Parsed.ppure_type))) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_se_ in
            let _endpos = _endpos_ty_ in
            let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_ty_ in
            let _startpos = _startpos_se_ in
            
# 419 "src/parsers/why_parser.mly"
    (  mk_type_cast (_startpos, _endpos) se ty )
# 7813 "src/parsers/why_parser.ml"
             in
            _menhir_goto_simple_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState186)
    | MenhirState303 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ID _v ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState304 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | COMMA | RIGHTPAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_id_, _menhir_s, (id : (string)), _startpos_id_), _endpos_ty_, _, (ty : (AltErgoLib.Parsed.ppure_type))) = _menhir_stack in
            let _2 = () in
            let _v : (AltErgoLib.Loc.t * string * AltErgoLib.Parsed.ppure_type) = 
# 218 "src/parsers/why_parser.mly"
    ( ((_startpos_id_, _endpos_id_), id, ty) )
# 7834 "src/parsers/why_parser.ml"
             in
            let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | COMMA ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | ID _v ->
                    _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState300 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState300)
            | RIGHTPAR ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, (binder : (AltErgoLib.Loc.t * string * AltErgoLib.Parsed.ppure_type))) = _menhir_stack in
                let _v : ((AltErgoLib.Loc.t * string * AltErgoLib.Parsed.ppure_type) list) = 
# 212 "src/parsers/why_parser.mly"
   ( [binder] )
# 7858 "src/parsers/why_parser.ml"
                 in
                _menhir_goto_list1_logic_binder_sep_comma _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState304)
    | MenhirState316 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState318
        | ID _v ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState318 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AXIOM | EOF | FUNC | GOAL | LOGIC | PRED | REWRITING | THEORY | TYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _endpos_ret_ty_, _menhir_s, (ret_ty : (AltErgoLib.Parsed.ppure_type))) = _menhir_stack in
            let _endpos = _endpos_ret_ty_ in
            let _v : (AltErgoLib.Parsed.plogic_type) = 
# 196 "src/parsers/why_parser.mly"
   ( mk_logic_type [] (Some ret_ty) )
# 7887 "src/parsers/why_parser.ml"
             in
            _menhir_goto_logic_type _menhir_env _menhir_stack _endpos _menhir_s _v
        | RIGHTARROW ->
            _menhir_reduce106 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState318)
    | MenhirState322 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ID _v ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState324 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AXIOM | EOF | FUNC | GOAL | LOGIC | PRED | REWRITING | THEORY | TYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (ty_list : (AltErgoLib.Parsed.ppure_type list))), _endpos_ret_ty_, _, (ret_ty : (AltErgoLib.Parsed.ppure_type))) = _menhir_stack in
            let _2 = () in
            let _endpos = _endpos_ret_ty_ in
            let _v : (AltErgoLib.Parsed.plogic_type) = 
# 193 "src/parsers/why_parser.mly"
   ( mk_logic_type ty_list (Some ret_ty) )
# 7911 "src/parsers/why_parser.ml"
             in
            _menhir_goto_logic_type _menhir_env _menhir_stack _endpos _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState324)
    | MenhirState334 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EQUAL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState335 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | CHECK ->
                _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState336 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | CUT ->
                _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState336 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DISTINCT ->
                _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState336 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | EXISTS ->
                _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState336 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FALSE ->
                _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState336 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FORALL ->
                _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState336 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState336 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | IF ->
                _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState336 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | INTEGER _v ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState336 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTBR ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState336 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTPAR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState336 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTSQ ->
                _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState336 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LET ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState336 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MATCH ->
                _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState336 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MINUS ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState336 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NOT ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState336 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NUM _v ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState336 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | STRING _v ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState336 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TRUE ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState336 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | VOID ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState336 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState336)
        | ID _v ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState335 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState335)
    | _ ->
        _menhir_fail ()

and _menhir_goto_list1_type_var_sep_comma : _menhir_env -> 'ttv_tail -> _menhir_state -> (string list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState7 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _endpos_alpha_, _menhir_s, (alpha : (string)), _startpos_alpha_), _, (l : (string list))) = _menhir_stack in
        let _2 = () in
        let _v : (string list) = 
# 529 "src/parsers/why_parser.mly"
                                                                ( alpha :: l )
# 7995 "src/parsers/why_parser.ml"
         in
        _menhir_goto_list1_type_var_sep_comma _menhir_env _menhir_stack _menhir_s _v
    | MenhirState5 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RIGHTPAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _menhir_s, _startpos__1_), _, (l : (string list))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (string list) = 
# 525 "src/parsers/why_parser.mly"
                                                ( l )
# 8015 "src/parsers/why_parser.ml"
             in
            _menhir_goto_type_vars _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_run2 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState2 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState2

and _menhir_goto_simple_expr : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (AltErgoLib.Parsed.lexpr) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState82 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COLON ->
            _menhir_run185 _menhir_env (Obj.magic _menhir_stack)
        | DOT ->
            _menhir_run183 _menhir_env (Obj.magic _menhir_stack)
        | LEFTSQ ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | QM ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | QM_ID _v ->
            _menhir_run117 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SHARP ->
            _menhir_run115 _menhir_env (Obj.magic _menhir_stack)
        | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState86 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState86)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState352 | MenhirState348 | MenhirState341 | MenhirState336 | MenhirState327 | MenhirState310 | MenhirState308 | MenhirState294 | MenhirState291 | MenhirState283 | MenhirState64 | MenhirState68 | MenhirState70 | MenhirState71 | MenhirState275 | MenhirState269 | MenhirState259 | MenhirState72 | MenhirState251 | MenhirState75 | MenhirState81 | MenhirState90 | MenhirState239 | MenhirState237 | MenhirState91 | MenhirState234 | MenhirState105 | MenhirState228 | MenhirState208 | MenhirState204 | MenhirState201 | MenhirState197 | MenhirState109 | MenhirState192 | MenhirState111 | MenhirState112 | MenhirState180 | MenhirState175 | MenhirState172 | MenhirState170 | MenhirState168 | MenhirState166 | MenhirState164 | MenhirState162 | MenhirState160 | MenhirState158 | MenhirState156 | MenhirState154 | MenhirState152 | MenhirState150 | MenhirState148 | MenhirState146 | MenhirState144 | MenhirState142 | MenhirState140 | MenhirState138 | MenhirState133 | MenhirState124 | MenhirState122 | MenhirState120 | MenhirState113 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COLON ->
            _menhir_run185 _menhir_env (Obj.magic _menhir_stack)
        | DOT ->
            _menhir_run183 _menhir_env (Obj.magic _menhir_stack)
        | LEFTSQ ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | QM ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | QM_ID _v ->
            _menhir_run117 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SHARP ->
            _menhir_run115 _menhir_env (Obj.magic _menhir_stack)
        | AND | AT | AXIOM | BAR | CASESPLIT | COMMA | ELSE | END | EOF | EQUAL | FUNC | GE | GOAL | GT | HAT | IN | LE | LEFTARROW | LOGIC | LRARROW | LT | MINUS | NOTEQ | OR | PERCENT | PLUS | POW | POWDOT | PRED | PV | REWRITING | RIGHTARROW | RIGHTBR | RIGHTPAR | RIGHTSQ | SLASH | THEN | THEORY | TIMES | TYPE | WITH | XOR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _endpos_se_, _menhir_s, (se : (AltErgoLib.Parsed.lexpr)), _startpos_se_) = _menhir_stack in
            let _startpos = _startpos_se_ in
            let _endpos = _endpos_se_ in
            let _v : (AltErgoLib.Parsed.lexpr) = 
# 237 "src/parsers/why_parser.mly"
                   ( se )
# 8103 "src/parsers/why_parser.ml"
             in
            _menhir_goto_lexpr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_run93 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 38 "src/parsers/why_parser.mly"
       (string)
# 8118 "src/parsers/why_parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | STRING _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (str : (
# 42 "src/parsers/why_parser.mly"
       (string)
# 8133 "src/parsers/why_parser.ml"
        )) = _v in
        let _startpos_str_ = _startpos in
        let (_menhir_stack, _endpos_id_, _menhir_s, (id : (
# 38 "src/parsers/why_parser.mly"
       (string)
# 8139 "src/parsers/why_parser.ml"
        )), _startpos_id_) = _menhir_stack in
        let _v : (string * string) = 
# 555 "src/parsers/why_parser.mly"
                       ( id, str )
# 8144 "src/parsers/why_parser.ml"
         in
        _menhir_goto_named_ident _menhir_env _menhir_stack _menhir_s _v
    | COLON | COMMA | EQUAL | LEFTPAR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _endpos_id_, _menhir_s, (id : (
# 38 "src/parsers/why_parser.mly"
       (string)
# 8152 "src/parsers/why_parser.ml"
        )), _startpos_id_) = _menhir_stack in
        let _v : (string * string) = 
# 554 "src/parsers/why_parser.mly"
          ( id, "" )
# 8157 "src/parsers/why_parser.ml"
         in
        _menhir_goto_named_ident _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run1 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LEFTPAR ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState1 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | QUOTE ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState1 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _ ->
        _menhir_reduce164 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState1

and _menhir_run57 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState57 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState57

and _menhir_run289 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState289 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState289

and _menhir_run296 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState296 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState296

and _menhir_run312 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AC ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _1 = () in
        let _v : (AltErgoLib.Symbols.name_kind) = 
# 167 "src/parsers/why_parser.mly"
        ( Symbols.Ac )
# 8237 "src/parsers/why_parser.ml"
         in
        _menhir_goto_ac_modifier _menhir_env _menhir_stack _v
    | ID _ ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _v : (AltErgoLib.Symbols.name_kind) = 
# 166 "src/parsers/why_parser.mly"
        ( Symbols.Other )
# 8245 "src/parsers/why_parser.ml"
         in
        _menhir_goto_ac_modifier _menhir_env _menhir_stack _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run325 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState325 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState325

and _menhir_run329 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState329 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState329

and _menhir_goto_file_parser : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 82 "src/parsers/why_parser.mly"
      (AltErgoLib.Parsed.file)
# 8284 "src/parsers/why_parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (_1 : (
# 82 "src/parsers/why_parser.mly"
      (AltErgoLib.Parsed.file)
# 8292 "src/parsers/why_parser.ml"
    )) = _v in
    Obj.magic _1

and _menhir_run339 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState339 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState339

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState352 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState348 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState346 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState341 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState339 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState336 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState335 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState334 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState331 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState329 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState327 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState325 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState324 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState322 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState318 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState316 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState314 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState310 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState308 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState304 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState303 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState300 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState298 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState296 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState294 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState291 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState289 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState287 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState283 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState281 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState275 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState273 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState269 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState266 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState262 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState259 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState257 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState256 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState253 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState251 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState242 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState239 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState237 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState234 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState232 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState228 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState225 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState224 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState214 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState211 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState208 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState204 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState201 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState197 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState192 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState186 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState185 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState183 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState180 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState175 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState172 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState170 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState168 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState166 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState164 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState162 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState160 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState158 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState156 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState154 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState152 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState150 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState148 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState146 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState144 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState142 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState140 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState138 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState133 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState124 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState122 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState120 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState118 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState115 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState113 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState112 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState111 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState109 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState108 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState107 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState106 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState105 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState104 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState102 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState101 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState99 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState96 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState92 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState91 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState90 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState86 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState82 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState81 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState75 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState73 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState72 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState71 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState70 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState68 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState64 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState62 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState61 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState59 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState57 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState53 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState50 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState47 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState46 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState44 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState43 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState42 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState40 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState38 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState33 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState32 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState24 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState21 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState18 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState14 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState13 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState11 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState7 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState5 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState2 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState1 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR

and _menhir_run65 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _1 = () in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos__1_ in
    let _startpos = _startpos__1_ in
    
# 380 "src/parsers/why_parser.mly"
              ( mk_void (_startpos, _endpos) )
# 8867 "src/parsers/why_parser.ml"
     in
    _menhir_goto_simple_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run66 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _1 = () in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos__1_ in
    let _startpos = _startpos__1_ in
    
# 378 "src/parsers/why_parser.mly"
              ( mk_true_const (_startpos, _endpos) )
# 8885 "src/parsers/why_parser.ml"
     in
    _menhir_goto_simple_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run67 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 42 "src/parsers/why_parser.mly"
       (string)
# 8892 "src/parsers/why_parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | COLON ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | CHECK ->
            _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | CUT ->
            _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DISTINCT ->
            _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | EXISTS ->
            _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | FALSE ->
            _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState68 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | FORALL ->
            _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | ID _v ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState68 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | IF ->
            _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | INTEGER _v ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState68 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LEFTBR ->
            _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LEFTPAR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LEFTSQ ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState68 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LET ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MATCH ->
            _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MINUS ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOT ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NUM _v ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState68 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | STRING _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TRUE ->
            _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState68 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | VOID ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState68 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState68)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run69 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 41 "src/parsers/why_parser.mly"
       (Num.num)
# 8958 "src/parsers/why_parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos_i_ = _endpos in
    let (i : (
# 41 "src/parsers/why_parser.mly"
       (Num.num)
# 8967 "src/parsers/why_parser.ml"
    )) = _v in
    let _startpos_i_ = _startpos in
    let _startpos = _startpos_i_ in
    let _endpos = _endpos_i_ in
    let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_i_ in
    let _startpos = _startpos_i_ in
    
# 377 "src/parsers/why_parser.mly"
              ( mk_real_const (_startpos, _endpos) i )
# 8977 "src/parsers/why_parser.ml"
     in
    _menhir_goto_simple_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run70 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHECK ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CUT ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DISTINCT ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXISTS ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState70 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FORALL ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState70 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState70 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTSQ ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState70 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LET ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState70 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRING _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState70 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState70 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState70

and _menhir_run71 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHECK ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CUT ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DISTINCT ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXISTS ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState71 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FORALL ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState71 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState71 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTSQ ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState71 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LET ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState71 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRING _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState71 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState71 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState71

and _menhir_run72 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHECK ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CUT ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DISTINCT ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXISTS ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState72 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FORALL ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState72 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState72 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTSQ ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState72 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LET ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState72 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRING _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState72 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState72 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState72

and _menhir_run73 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState73 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState73

and _menhir_run76 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BAR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | INTEGER _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BAR ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | RIGHTSQ ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _endpos__5_ = _endpos in
                    let ((_menhir_stack, _endpos__1_, _menhir_s, _startpos__1_), _endpos_bv_cst_, (bv_cst : (
# 40 "src/parsers/why_parser.mly"
       (string)
# 9180 "src/parsers/why_parser.ml"
                    )), _startpos_bv_cst_) = _menhir_stack in
                    let _5 = () in
                    let _4 = () in
                    let _2 = () in
                    let _1 = () in
                    let _startpos = _startpos__1_ in
                    let _endpos = _endpos__5_ in
                    let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos__5_ in
                    let _startpos = _startpos__1_ in
                    
# 304 "src/parsers/why_parser.mly"
    ( mk_bitv_const (_startpos, _endpos) bv_cst )
# 9193 "src/parsers/why_parser.ml"
                     in
                    _menhir_goto_lexpr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let ((_menhir_stack, _, _menhir_s, _), _, _, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _, _menhir_s, _), _, _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run81 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHECK ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CUT ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DISTINCT ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXISTS ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState81 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FORALL ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState81 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState81 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTSQ ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState81 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LET ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState81 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRING _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState81 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState81 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState81

and _menhir_run82 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState82 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState82 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState82 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState82

and _menhir_run83 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 40 "src/parsers/why_parser.mly"
       (string)
# 9302 "src/parsers/why_parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos_i_ = _endpos in
    let (i : (
# 40 "src/parsers/why_parser.mly"
       (string)
# 9311 "src/parsers/why_parser.ml"
    )) = _v in
    let _startpos_i_ = _startpos in
    let _startpos = _startpos_i_ in
    let _endpos = _endpos_i_ in
    let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_i_ in
    let _startpos = _startpos_i_ in
    
# 376 "src/parsers/why_parser.mly"
              ( mk_int_const (_startpos, _endpos) i )
# 9321 "src/parsers/why_parser.ml"
     in
    _menhir_goto_simple_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run91 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHECK ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CUT ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DISTINCT ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXISTS ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState91 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FORALL ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState91 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState91 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTSQ ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState91 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LET ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState91 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRING _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState91 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState91 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState91

and _menhir_run3 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 38 "src/parsers/why_parser.mly"
       (string)
# 9379 "src/parsers/why_parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos_id_ = _endpos in
    let (id : (
# 38 "src/parsers/why_parser.mly"
       (string)
# 9388 "src/parsers/why_parser.ml"
    )) = _v in
    let _startpos_id_ = _startpos in
    let _startpos = _startpos_id_ in
    let _endpos = _endpos_id_ in
    let _v : (string) = 
# 532 "src/parsers/why_parser.mly"
          ( id )
# 9396 "src/parsers/why_parser.ml"
     in
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState2 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos_alpha_, _, (alpha : (string)), _startpos_alpha_) = _menhir_stack in
        let _1 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_alpha_ in
        let _v : (string) = 
# 520 "src/parsers/why_parser.mly"
                      ( alpha )
# 9410 "src/parsers/why_parser.ml"
         in
        let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
        (match _menhir_s with
        | MenhirState7 | MenhirState5 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | COMMA ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | QUOTE ->
                    _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState7 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState7)
            | RIGHTPAR ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _endpos_alpha_, _menhir_s, (alpha : (string)), _startpos_alpha_) = _menhir_stack in
                let _v : (string list) = 
# 528 "src/parsers/why_parser.mly"
                                                  ( [alpha] )
# 9436 "src/parsers/why_parser.ml"
                 in
                _menhir_goto_list1_type_var_sep_comma _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | MenhirState334 | MenhirState322 | MenhirState316 | MenhirState303 | MenhirState185 | MenhirState101 | MenhirState21 | MenhirState33 | MenhirState24 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _endpos_alpha_, _menhir_s, (alpha : (string)), _startpos_alpha_) = _menhir_stack in
            let _endpos = _endpos_alpha_ in
            let _v : (AltErgoLib.Parsed.ppure_type) = let _endpos = _endpos_alpha_ in
            let _startpos = _startpos_alpha_ in
            
# 178 "src/parsers/why_parser.mly"
                   ( mk_var_type (_startpos, _endpos) alpha )
# 9455 "src/parsers/why_parser.ml"
             in
            _menhir_goto_primitive_type _menhir_env _menhir_stack _endpos _menhir_s _v
        | MenhirState1 | MenhirState43 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _endpos_alpha_, _menhir_s, (alpha : (string)), _startpos_alpha_) = _menhir_stack in
            let _v : (string list) = 
# 524 "src/parsers/why_parser.mly"
                    ( [alpha] )
# 9465 "src/parsers/why_parser.ml"
             in
            _menhir_goto_type_vars _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            _menhir_fail ())
    | MenhirState11 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EQUAL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState13 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTBR ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState13 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState13)
        | AXIOM | EOF | FUNC | GOAL | LOGIC | PRED | REWRITING | THEORY | TYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, _startpos__1_), _, (ty_vars : (string list))), _endpos_ty_, _, (ty : (string)), _startpos_ty_) = _menhir_stack in
            let _1 = () in
            let _v : (AltErgoLib.Parsed.decl) = let _endpos = _endpos_ty_ in
            let _startpos = _startpos__1_ in
            
# 105 "src/parsers/why_parser.mly"
    ( mk_abstract_type_decl (_startpos, _endpos) ty_vars ty )
# 9497 "src/parsers/why_parser.ml"
             in
            _menhir_goto_decl _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState14 | MenhirState18 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BITV ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState21
            | BOOL ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState21
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState21 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | INT ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState21
            | LEFTPAR ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState21 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | QUOTE ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState21 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | REAL ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState21
            | UNIT ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState21
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState21)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState334 | MenhirState316 | MenhirState322 | MenhirState303 | MenhirState185 | MenhirState101 | MenhirState21 | MenhirState24 | MenhirState33 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _endpos_ext_ty_, _menhir_s, (ext_ty : (string)), _startpos_ext_ty_) = _menhir_stack in
        let _endpos = _endpos_ext_ty_ in
        let _v : (AltErgoLib.Parsed.ppure_type) = let _endpos = _endpos_ext_ty_ in
        let _startpos = _startpos_ext_ty_ in
        
# 176 "src/parsers/why_parser.mly"
                 ( mk_external_type (_startpos, _endpos) [] ext_ty )
# 9552 "src/parsers/why_parser.ml"
         in
        _menhir_goto_primitive_type _menhir_env _menhir_stack _endpos _menhir_s _v
    | MenhirState335 | MenhirState324 | MenhirState318 | MenhirState304 | MenhirState186 | MenhirState102 | MenhirState40 | MenhirState32 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _endpos_par_, _menhir_s, (par : (AltErgoLib.Parsed.ppure_type))), _endpos_ext_ty_, _, (ext_ty : (string)), _startpos_ext_ty_) = _menhir_stack in
        let _endpos = _endpos_ext_ty_ in
        let _v : (AltErgoLib.Parsed.ppure_type) = 
# 181 "src/parsers/why_parser.mly"
   ( mk_external_type (_startpos_ext_ty_, _endpos_ext_ty_) [par] ext_ty )
# 9563 "src/parsers/why_parser.ml"
         in
        _menhir_goto_primitive_type _menhir_env _menhir_stack _endpos _menhir_s _v
    | MenhirState38 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((_menhir_stack, _menhir_s, _startpos__1_), _, (pars : (AltErgoLib.Parsed.ppure_type list))), _endpos__3_), _endpos_ext_ty_, _, (ext_ty : (string)), _startpos_ext_ty_) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _endpos = _endpos_ext_ty_ in
        let _v : (AltErgoLib.Parsed.ppure_type) = 
# 184 "src/parsers/why_parser.mly"
   ( mk_external_type (_startpos_ext_ty_, _endpos_ext_ty_) pars ext_ty )
# 9576 "src/parsers/why_parser.ml"
         in
        _menhir_goto_primitive_type _menhir_env _menhir_stack _endpos _menhir_s _v
    | MenhirState44 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EQUAL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState46 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState46)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState13 | MenhirState53 | MenhirState46 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | OF ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LEFTBR ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState50 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState50)
        | AND | AXIOM | BAR | EOF | FUNC | GOAL | LOGIC | PRED | REWRITING | THEORY | TYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_, _endpos) = Obj.magic _menhir_stack in
            let _v : ((string * AltErgoLib.Parsed.ppure_type) list) = 
# 226 "src/parsers/why_parser.mly"
  ( [] )
# 9623 "src/parsers/why_parser.ml"
             in
            _menhir_goto_algebraic_args _menhir_env _menhir_stack _endpos _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState57 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EXTENDS ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState59 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState59)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState59 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EQUAL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AXIOM ->
                _menhir_run281 _menhir_env (Obj.magic _menhir_stack) MenhirState61 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | CASESPLIT ->
                _menhir_run62 _menhir_env (Obj.magic _menhir_stack) MenhirState61 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | END ->
                _menhir_reduce157 _menhir_env (Obj.magic _menhir_stack) MenhirState61
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState61)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState62 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | CHECK ->
                _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | CUT ->
                _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DISTINCT ->
                _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | EXISTS ->
                _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FALSE ->
                _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FORALL ->
                _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | IF ->
                _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | INTEGER _v ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTBR ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTPAR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTSQ ->
                _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LET ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MATCH ->
                _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MINUS ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NOT ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NUM _v ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | STRING _v ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState64 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TRUE ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | VOID ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState64)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState242 | MenhirState86 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EQUAL ->
            _menhir_run90 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState115 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _endpos_se_, _menhir_s, (se : (AltErgoLib.Parsed.lexpr)), _startpos_se_), _endpos_label_, _, (label : (string)), _startpos_label_) = _menhir_stack in
        let _2 = () in
        let _startpos = _startpos_se_ in
        let _endpos = _endpos_label_ in
        let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_label_ in
        let _startpos = _startpos_se_ in
        
# 428 "src/parsers/why_parser.mly"
   ( mk_algebraic_project (_startpos, _endpos) ~guarded:true se label )
# 9765 "src/parsers/why_parser.ml"
         in
        _menhir_goto_simple_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | MenhirState118 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _endpos_se_, _menhir_s, (se : (AltErgoLib.Parsed.lexpr)), _startpos_se_), _endpos__2_, _startpos__2_), _endpos_id_, _, (id : (string)), _startpos_id_) = _menhir_stack in
        let _2 = () in
        let _startpos = _startpos_se_ in
        let _endpos = _endpos_id_ in
        let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_id_ in
        let _startpos = _startpos_se_ in
        
# 422 "src/parsers/why_parser.mly"
    ( mk_algebraic_test (_startpos, _endpos) se id )
# 9780 "src/parsers/why_parser.ml"
         in
        _menhir_goto_simple_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | MenhirState348 | MenhirState341 | MenhirState336 | MenhirState327 | MenhirState310 | MenhirState308 | MenhirState291 | MenhirState294 | MenhirState283 | MenhirState64 | MenhirState68 | MenhirState70 | MenhirState71 | MenhirState72 | MenhirState275 | MenhirState269 | MenhirState259 | MenhirState251 | MenhirState75 | MenhirState81 | MenhirState90 | MenhirState91 | MenhirState237 | MenhirState239 | MenhirState234 | MenhirState228 | MenhirState201 | MenhirState109 | MenhirState197 | MenhirState111 | MenhirState192 | MenhirState112 | MenhirState113 | MenhirState180 | MenhirState120 | MenhirState175 | MenhirState122 | MenhirState133 | MenhirState172 | MenhirState140 | MenhirState170 | MenhirState152 | MenhirState168 | MenhirState166 | MenhirState164 | MenhirState162 | MenhirState160 | MenhirState158 | MenhirState154 | MenhirState156 | MenhirState146 | MenhirState150 | MenhirState148 | MenhirState144 | MenhirState142 | MenhirState138 | MenhirState124 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LEFTPAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AND | AT | AXIOM | BAR | CASESPLIT | COLON | COMMA | DOT | ELSE | END | EOF | EQUAL | FUNC | GE | GOAL | GT | HAT | IN | LE | LEFTARROW | LEFTSQ | LOGIC | LRARROW | LT | MINUS | NOTEQ | OR | PERCENT | PLUS | POW | POWDOT | PRED | PV | QM | QM_ID _ | REWRITING | RIGHTARROW | RIGHTBR | RIGHTPAR | RIGHTSQ | SHARP | SLASH | THEN | THEORY | TIMES | TYPE | WITH | XOR ->
            _menhir_reduce139 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState183 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _endpos_se_, _menhir_s, (se : (AltErgoLib.Parsed.lexpr)), _startpos_se_), _endpos_label_, _, (label : (string)), _startpos_label_) = _menhir_stack in
        let _2 = () in
        let _startpos = _startpos_se_ in
        let _endpos = _endpos_label_ in
        let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos_label_ in
        let _startpos = _startpos_se_ in
        
# 392 "src/parsers/why_parser.mly"
   ( mk_dot_record (_startpos, _endpos) se label )
# 9810 "src/parsers/why_parser.ml"
         in
        _menhir_goto_simple_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | MenhirState352 | MenhirState105 | MenhirState204 | MenhirState208 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LEFTPAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MAPS_TO ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | CHECK ->
                _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState228 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | CUT ->
                _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState228 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DISTINCT ->
                _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState228 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | EXISTS ->
                _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState228 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FALSE ->
                _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState228 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FORALL ->
                _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState228 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState228 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | IF ->
                _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState228 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | INTEGER _v ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState228 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTBR ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState228 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTPAR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState228 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTSQ ->
                _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState228 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LET ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState228 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MATCH ->
                _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState228 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MINUS ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState228 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NOT ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState228 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NUM _v ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState228 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | STRING _v ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState228 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TRUE ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState228 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | VOID ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState228 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState228)
        | AND | AT | BAR | COLON | COMMA | DOT | EOF | EQUAL | GE | GT | HAT | IN | LE | LEFTSQ | LRARROW | LT | MINUS | NOTEQ | OR | PERCENT | PLUS | POW | POWDOT | QM | QM_ID _ | RIGHTARROW | RIGHTSQ | SHARP | SLASH | TIMES | XOR ->
            _menhir_reduce139 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState82 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EQUAL ->
            _menhir_run90 _menhir_env (Obj.magic _menhir_stack)
        | LEFTPAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | COLON | DOT | LEFTSQ | QM | QM_ID _ | SHARP | WITH ->
            _menhir_reduce139 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState253 | MenhirState73 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EQUAL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | CHECK ->
                _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState251 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | CUT ->
                _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState251 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DISTINCT ->
                _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState251 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | EXISTS ->
                _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState251 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FALSE ->
                _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState251 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FORALL ->
                _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState251 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState251 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | IF ->
                _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState251 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | INTEGER _v ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState251 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTBR ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState251 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTPAR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState251 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTSQ ->
                _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState251 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LET ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState251 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MATCH ->
                _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState251 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MINUS ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState251 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NOT ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState251 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NUM _v ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState251 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | STRING _v ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState251 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TRUE ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState251 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | VOID ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState251 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState251)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState256 | MenhirState273 | MenhirState257 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LEFTPAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState262 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState262)
        | RIGHTARROW ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _endpos_id_, _menhir_s, (id : (string)), _startpos_id_) = _menhir_stack in
            let _v : (AltErgoLib.Parsed.pattern) = let _endpos = _endpos_id_ in
            let _startpos = _startpos_id_ in
            
# 366 "src/parsers/why_parser.mly"
             ( mk_pattern (_startpos, _endpos) id [] )
# 9980 "src/parsers/why_parser.ml"
             in
            _menhir_goto_simple_pattern _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState266 | MenhirState262 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState266 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState266)
        | RIGHTPAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _endpos_id_, _menhir_s, (id : (string)), _startpos_id_) = _menhir_stack in
            let _v : (string list) = 
# 550 "src/parsers/why_parser.mly"
    ( [ id ] )
# 10011 "src/parsers/why_parser.ml"
             in
            _menhir_goto_list1_string_sep_comma _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState281 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | CHECK ->
                _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState283 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | CUT ->
                _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState283 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DISTINCT ->
                _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState283 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | EXISTS ->
                _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState283 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FALSE ->
                _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState283 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FORALL ->
                _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState283 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState283 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | IF ->
                _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState283 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | INTEGER _v ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState283 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTBR ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState283 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTPAR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState283 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTSQ ->
                _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState283 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LET ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState283 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MATCH ->
                _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState283 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MINUS ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState283 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NOT ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState283 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NUM _v ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState283 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | STRING _v ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState283 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TRUE ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState283 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | VOID ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState283 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState283)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState289 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | CHECK ->
                _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState291 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | CUT ->
                _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState291 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DISTINCT ->
                _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState291 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | EXISTS ->
                _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState291 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FALSE ->
                _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState291 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FORALL ->
                _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState291 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState291 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | IF ->
                _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState291 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | INTEGER _v ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState291 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTBR ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState291 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTPAR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState291 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTSQ ->
                _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState291 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LET ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState291 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MATCH ->
                _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState291 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MINUS ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState291 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NOT ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState291 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NUM _v ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState291 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | STRING _v ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState291 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TRUE ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState291 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | VOID ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState291 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState291)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState331 | MenhirState298 | MenhirState300 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BITV ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState303
            | BOOL ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState303
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState303 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | INT ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState303
            | LEFTPAR ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState303 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | QUOTE ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState303 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | REAL ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState303
            | UNIT ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState303
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState303)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState325 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | CHECK ->
                _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState327 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | CUT ->
                _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState327 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DISTINCT ->
                _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState327 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | EXISTS ->
                _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState327 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FALSE ->
                _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState327 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FORALL ->
                _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState327 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState327 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | IF ->
                _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState327 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | INTEGER _v ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState327 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTBR ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState327 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTPAR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState327 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTSQ ->
                _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState327 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LET ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState327 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MATCH ->
                _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState327 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MINUS ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState327 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NOT ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState327 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NUM _v ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState327 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | STRING _v ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState327 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TRUE ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState327 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | VOID ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState327 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState327)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState339 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | CHECK ->
                _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState341 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | CUT ->
                _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState341 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DISTINCT ->
                _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState341 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | EXISTS ->
                _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState341 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FALSE ->
                _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState341 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FORALL ->
                _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState341 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | ID _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState341 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | IF ->
                _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState341 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | INTEGER _v ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState341 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTBR ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState341 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTPAR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState341 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LEFTSQ ->
                _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState341 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LET ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState341 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MATCH ->
                _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState341 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MINUS ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState341 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NOT ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState341 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NUM _v ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState341 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | STRING _v ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState341 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TRUE ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState341 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | VOID ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState341 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState341)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_run92 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState92 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState92

and _menhir_run84 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _1 = () in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (AltErgoLib.Parsed.lexpr) = let _endpos = _endpos__1_ in
    let _startpos = _startpos__1_ in
    
# 379 "src/parsers/why_parser.mly"
              ( mk_false_const (_startpos, _endpos) )
# 10326 "src/parsers/why_parser.ml"
     in
    _menhir_goto_simple_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run106 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState106 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState106

and _menhir_run110 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LEFTPAR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | CHECK ->
            _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState111 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | CUT ->
            _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState111 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DISTINCT ->
            _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState111 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | EXISTS ->
            _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState111 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | FALSE ->
            _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState111 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | FORALL ->
            _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState111 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | ID _v ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState111 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | IF ->
            _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState111 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | INTEGER _v ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState111 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LEFTBR ->
            _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState111 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LEFTPAR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState111 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LEFTSQ ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState111 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LET ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState111 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MATCH ->
            _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState111 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MINUS ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState111 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOT ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState111 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NUM _v ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState111 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | STRING _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState111 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TRUE ->
            _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState111 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | VOID ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState111 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState111)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run112 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHECK ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState112 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CUT ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState112 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DISTINCT ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState112 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXISTS ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState112 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState112 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FORALL ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState112 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState112 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState112 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState112 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState112 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState112 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTSQ ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState112 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LET ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState112 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState112 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState112 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState112 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState112 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRING _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState112 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState112 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState112 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState112

and _menhir_run113 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHECK ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState113 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CUT ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState113 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DISTINCT ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState113 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXISTS ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState113 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState113 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FORALL ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState113 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState113 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState113 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState113 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState113 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState113 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTSQ ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState113 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LET ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState113 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState113 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState113 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState113 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState113 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRING _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState113 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState113 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState113 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState113

and _menhir_discard : _menhir_env -> _menhir_env =
  fun _menhir_env ->
    let lexer = _menhir_env._menhir_lexer in
    let lexbuf = _menhir_env._menhir_lexbuf in
    let _tok = lexer lexbuf in
    {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = _tok;
      _menhir_error = false;
    }

and _menhir_init : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> _menhir_env =
  fun lexer lexbuf ->
    let _tok = Obj.magic () in
    {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = _tok;
      _menhir_error = false;
    }

and file_parser : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (
# 82 "src/parsers/why_parser.mly"
      (AltErgoLib.Parsed.file)
# 10534 "src/parsers/why_parser.ml"
) =
  fun lexer lexbuf ->
    let _menhir_env = _menhir_init lexer lexbuf in
    Obj.magic (let _menhir_stack = ((), _menhir_env._menhir_lexbuf.Lexing.lex_curr_p) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AXIOM ->
        _menhir_run339 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EOF ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState0 in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _1 = () in
        let _v : (
# 82 "src/parsers/why_parser.mly"
      (AltErgoLib.Parsed.file)
# 10552 "src/parsers/why_parser.ml"
        ) = 
# 88 "src/parsers/why_parser.mly"
      ( [] )
# 10556 "src/parsers/why_parser.ml"
         in
        _menhir_goto_file_parser _menhir_env _menhir_stack _menhir_s _v
    | FUNC ->
        _menhir_run329 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | GOAL ->
        _menhir_run325 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LOGIC ->
        _menhir_run312 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | PRED ->
        _menhir_run296 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | REWRITING ->
        _menhir_run289 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | THEORY ->
        _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TYPE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState0)

and lexpr_parser : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (
# 79 "src/parsers/why_parser.mly"
      (AltErgoLib.Parsed.lexpr)
# 10581 "src/parsers/why_parser.ml"
) =
  fun lexer lexbuf ->
    let _menhir_env = _menhir_init lexer lexbuf in
    Obj.magic (let _menhir_stack = ((), _menhir_env._menhir_lexbuf.Lexing.lex_curr_p) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHECK ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState348 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CUT ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState348 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DISTINCT ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState348 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXISTS ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState348 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState348 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FORALL ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState348 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState348 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState348 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState348 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState348 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState348 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTSQ ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState348 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LET ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState348 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState348 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState348 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState348 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState348 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRING _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState348 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState348 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState348 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState348)

and trigger_parser : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (
# 76 "src/parsers/why_parser.mly"
      (AltErgoLib.Parsed.lexpr list * bool)
# 10637 "src/parsers/why_parser.ml"
) =
  fun lexer lexbuf ->
    let _menhir_env = _menhir_init lexer lexbuf in
    Obj.magic (let _menhir_stack = ((), _menhir_env._menhir_lexbuf.Lexing.lex_curr_p) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHECK ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState352 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CUT ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState352 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DISTINCT ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState352 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXISTS ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState352 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FALSE ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState352 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FORALL ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState352 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState352 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState352 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState352 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTBR ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState352 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTPAR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState352 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LEFTSQ ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState352 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LET ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState352 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState352 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState352 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState352 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUM _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState352 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRING _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState352 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TRUE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState352 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VOID ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState352 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState352)

# 269 "<standard.mly>"
  

# 10693 "src/parsers/why_parser.ml"
