(* The run-time library for parsers generated by camlyacc *)

val symbol_start : unit -> int
val symbol_end : unit -> int
        (* [symbol_start] and [symbol_end] are to be called in the action part
           of a grammar rule only. They return the position of the string that
           matches the left-hand side of the rule: [symbol_start()] returns
           the position of the first character; [symbol_end()] returns the
           position of the last character, plus one. The first character
           in a file is at position 0. *)
val rhs_start: int -> int
val rhs_end: int -> int
        (* Same as [symbol_start] and [symbol_end] above, but return then
           position of the string matching the [n]th item on the
           right-hand side of the rule, where [n] is the integer parameter
           to [lhs_start] and [lhs_end]. [n] is 1 for the leftmost item. *)
val clear_parser : unit -> unit
        (* Empty the parser stack. Call it just after a parsing function
           has returned, to remove all pointers from the parser stack
           to structures that were built by semantic actions during parsing.
           This is optional, but lowers the memory requirements of the
           programs. *)

exception Parse_error
        (* Raised when a parser encounters a syntax error. *)

(*--*)

(* The following definitions are used by the generated parsers only.
   They are not intended to be used by user programs. *)

type parse_tables =
  { actions : (unit -> Obj.t) array;
    transl_const : int array;
    transl_block : int array;
    lhs : string;
    len : string;
    defred : string;
    dgoto : string;
    sindex : string;
    rindex : string;
    gindex : string;
    tablesize : int;
    table : string;
    check : string }

exception YYexit of Obj.t

val yyparse :
      parse_tables -> int -> (Lexing.lexbuf -> 'a) -> Lexing.lexbuf -> 'b
val peek_val : int -> 'a
val is_current_lookahead: 'a -> bool
