(***********************************************************************)
(*                                                                     *)
(*                           Objective Caml                            *)
(*                                                                     *)
(*                 Marcell Fischbach, University of Siegen             *)
(*                  Benedikt Meurer, University of Siegen              *)
(*                                                                     *)
(*    Copyright 2011 Lehrstuhl für Compilerbau und Softwareanalyse,    *)
(*    Universität Siegen. All rights reserved. This file is distri-    *)
(*    buted under the terms of the Q Public License version 1.0.       *)
(*                                                                     *)
(***********************************************************************)

(* $Id$ *)

(* Live intervals for the linear scan register allocator. *)

type range =
  {
    mutable rbegin: int;
    mutable rend: int;
  }

type t = 
  { 
    mutable reg: Reg.t;
    mutable ibegin: int;
    mutable iend: int;
    mutable ranges: range list;
  }

val all_intervals: unit -> t list
val all_fixed_intervals: unit -> t list
val build_intervals: Mach.fundecl -> unit
val live_on: t -> int -> bool
val overlapping_ranges: range -> range -> bool
val overlapping: t -> t -> bool
val strip_expired_ranges: range list -> int -> range list
