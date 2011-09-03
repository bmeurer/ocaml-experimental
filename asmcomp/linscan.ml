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

(* Linear scan register allocation. *)

open Interval
open Clflags
open List
open Format
open Mach

(* Live intervals per register class *)

type class_intervals =
  {
    mutable ci_fixed: Interval.t list;
    mutable ci_active: Interval.t list;
    mutable ci_inactive: Interval.t list;
  }

let active = Array.init Proc.num_register_classes (fun _ -> {
  ci_fixed = [];
  ci_active = [];
  ci_inactive = []
})

(* Insert interval into list sorted by end position *)

let rec insert_interval_sorted i = function
    [] -> [i]
  | j :: _ as il when j.iend <= i.iend -> i :: il
  | j :: il -> j :: insert_interval_sorted i il

let rec release_expired_fixed pos = function
    i :: il when i.iend > pos ->
      i.ranges <- Interval.strip_expired_ranges i.ranges pos;
      i :: release_expired_fixed pos il
  | _ -> []

let rec release_expired_active ci pos = function
    i :: il when i.iend > pos ->
      i.ranges <- Interval.strip_expired_ranges i.ranges pos;
      if Interval.live_on i pos then
        i :: release_expired_active ci pos il
      else begin
        ci.ci_inactive <- insert_interval_sorted i ci.ci_inactive;
        release_expired_active ci pos il
      end
  | _ -> []

let rec release_expired_inactive ci pos = function
    i :: il when i.iend > pos ->
      i.ranges <- Interval.strip_expired_ranges i.ranges pos;
      if not (Interval.live_on i pos) then 
        i :: release_expired_inactive ci pos il
      else begin
        ci.ci_active <- insert_interval_sorted i ci.ci_active;
        release_expired_inactive ci pos il
      end
  | _ -> []

let get_stack_slot cl = 
  let nslots = Proc.num_stack_slots.(cl) in
  Proc.num_stack_slots.(cl) <- nslots + 1;
  nslots
    


(* find a register for the given interval and assigns this
   register. The interval is inserted into active.
   If there is no space available for this interval then
   nothings happens and false is returned. Otherwise 
   returns true.
   *)
let try_alloc_free_register interval  =
  let cl = Proc.register_class interval.reg in
  (* this intervals has already been spilled *)
  if interval.reg.Reg.spill then begin
    begin match interval.reg.Reg.loc with
    | Reg.Unknown -> interval.reg.Reg.loc <- Reg.Stack(Reg.Local (get_stack_slot cl));
    | _ -> ()
    end
  end;
  
  let num = Proc.num_available_registers.(cl) in
  if interval.reg.Reg.loc != Reg.Unknown then true (* this register is already allocated or spilled *)
  else if num = 0 then false (* there are not registers for this class *)
  else begin
    let first_reg = Proc.first_available_register.(cl) in
    let ci = active.(cl) in

    (* create array containing all possible free regs *)
    let regs = Array.make num true in
    
    (* remove all assigned registers from the free array *)
    let rec remove_bound actives =
      begin match actives with
      | [] -> ()
      | i::tl ->
        begin
          begin match i.reg.Reg.loc with
          | Reg.Reg(r) -> regs.(r - first_reg) <- false
          | _ -> ()
          end;
          remove_bound tl
        end
      end
    in

    remove_bound ci.ci_active;
      
    (* remove all overlapping registers from the free array *)
    let rec remove_bound_overlapping fix =
      begin match fix with
      | [] -> ()
      | i::tl ->
        begin
          begin match i.reg.Reg.loc with
          | Reg.Reg(r) -> 
              if regs.(r-first_reg) && Interval.overlapping i interval then 
                regs.(r - first_reg) <- false
          | _ -> ()
          end;
          remove_bound_overlapping tl
        end
      end
    in
    remove_bound_overlapping ci.ci_inactive;
    remove_bound_overlapping ci.ci_fixed;
      

    let rec find_first_free_reg c =
      if c = num then -1
      else if regs.(c) then c
      else find_first_free_reg (c+1) in

    let first_free_reg = find_first_free_reg 0 in
    
    if first_free_reg = -1 then false
    else begin
      (* assign the free register *)
      interval.reg.Reg.loc <- Reg.Reg (first_reg + first_free_reg);
      interval.reg.Reg.spill <- false;
      (* and insert the current interval into active *)
      ci.ci_active <- insert_interval_sorted interval ci.ci_active;
      true
    end;
  end
 
let allocate_blocked_register i =
  let cl = Proc.register_class i.reg in
  let ci = active.(cl) in
  begin match ci.ci_active with
    ilast :: il when ilast.iend > i.iend ->
      (* Last interval in active is the last interval, so spill it. *)
      begin match ilast.reg.Reg.loc with 
        Reg.Reg r ->
          (* Use register from last interval for current interval *)
          i.reg.Reg.loc <- Reg.Reg r
      | _ -> ()
      end;
      (* Remove the last interval from active and insert the current *)
      ci.ci_active <- insert_interval_sorted i il;
      (* Now get a new stack slot for the spilled register *)
      ilast.reg.Reg.loc <- Reg.Stack(Reg.Local(get_stack_slot cl));
      ilast.reg.Reg.spill <- true
  | _ ->
      (* Either the current interval is last and we have to spill it,
         or there are no registers at all in the register class (i.e.
         floating point class on i386). *)
      i.reg.Reg.loc <- Reg.Stack(Reg.Local(get_stack_slot cl));
      i.reg.Reg.spill <- true
  end

let handle_interval i =
  let pos = i.ibegin in
  (* Release all intervals that have been expired at the current position *)
  for cl = 0 to Proc.num_register_classes - 1 do
    let ci = active.(cl) in
    ci.ci_fixed <- release_expired_fixed pos ci.ci_fixed;
    ci.ci_active <- release_expired_active ci pos ci.ci_active;
    ci.ci_inactive <- release_expired_inactive ci pos ci.ci_inactive
  done;
  (* Find a register to allocate *)
  if not (try_alloc_free_register i) then
    (* No free register, need to decide which interval to spill *)
    allocate_blocked_register i

let allocate_registers() =
  (* Initialize the stack slots and interval lists *)
  for cl = 0 to Proc.num_register_classes - 1 do
    (* Start with empty interval lists *)
    active.(cl) <- {
      ci_fixed = [];
      ci_active = [];
      ci_inactive = []
    };
    Proc.num_stack_slots.(cl) <- 0
  done;
  (* Add all fixed intervals (sorted by end position) *)
  List.iter
    (fun i ->
      let ci = active.(Proc.register_class i.reg) in
      ci.ci_fixed <- insert_interval_sorted i ci.ci_fixed)
    (Interval.all_fixed_intervals());
  (* Walk all the intervals within the list *)
  List.iter handle_interval (Interval.all_intervals())
