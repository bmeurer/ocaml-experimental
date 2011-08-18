(***********************************************************************)
(*                                                                     *)
(*                           Objective Caml                            *)
(*                                                                     *)
(*                          Marcell Fischbach                          *)
(*                                                                     *)
(*  Copyright 2011 University of Siegen. All rights reserved.          *)
(*  This file is distributed  under the terms of the                   *)
(*  Q Public License version 1.0.                                      *)
(*                                                                     *)
(***********************************************************************)



open Format

 
type range =
  {
    mutable rbegin : int;
    mutable rend : int;
  }

type interval = 
  { 
      mutable reg : Reg.t;
      mutable ibegin : int;
      mutable iend : int;
      mutable ranges : range list;
  }


val all_intervals : unit -> interval list
val all_fixed_intervals: unit -> interval list
val debug_intervals: formatter ->  Mach.fundecl -> unit
val build_intervals: Mach.fundecl -> unit
val live_on: interval -> int -> bool
val overlapping_ranges: range -> range -> bool
val overlapping: interval -> interval -> bool
val strip_expired_ranges: range list -> int -> range list
