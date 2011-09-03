(***********************************************************************)
(*                                                                     *)
(*                           Objective Caml                            *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1997 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* $Id$ *)

(* Auxiliary type for reporting syntax errors *)

open Format

type error =
    Unclosed of Location.t * string * Location.t * string
  | Applicative_path of Location.t
  | Other of Location.t

exception Error of error
exception Escape_error

let report_error ppf = function
  | Unclosed(opening_loc, opening, closing_loc, closing) ->
      if String.length !Location.input_name = 0
      && Location.highlight_locations ppf opening_loc closing_loc
      then fprintf ppf "Syntax error: '%s' expected, \
                   the highlighted '%s' might be unmatched" closing opening
      else begin
        fprintf ppf "%aSyntax error: '%s' expected@."
          Location.print_error closing_loc closing;
        fprintf ppf "%aThis '%s' might be unmatched"
          Location.print_error opening_loc opening
      end
  | Applicative_path loc ->
      fprintf ppf "%aSyntax error: applicative paths of the form F(X).t are not supported when the option -no-app-func is set."
        Location.print_error loc
  | Other loc ->
      fprintf ppf "%aSyntax error" Location.print_error loc
