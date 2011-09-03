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

open List
open Mach
open Reg

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


let interval_list = ref ([] : interval list)
let fixed_interval_list = ref ([] : interval list)
let all_intervals() = !interval_list
let all_fixed_intervals() = !fixed_interval_list

let overlapping_ranges r0 r1 =
  r0.rend > r1.rbegin && r1.rend > r0.rbegin


let overlapping i0 i1 =

  let rec test_ranges r0s r1s =
    begin match r0s, r1s with
    | [], _ -> false
    | _, [] -> false
    | r0::r0tl, r1::r1tl ->
      if overlapping_ranges r0 r1 then true
      else if r0.rend < r1.rend then test_ranges r0tl r1s
      else if r0.rend > r1.rend then test_ranges r0s r1tl
      else test_ranges r0tl r1tl
    end 
  in

  test_ranges i0.ranges i1.ranges

let live_on i p = 
  let rec live_on_ranges r =
    begin match r with
    | [] -> false
    | hd::tl -> 
          if p < hd.rbegin then false
          else if p < hd.rend then true
          else live_on_ranges tl
    end in
  live_on_ranges i.ranges
 

let rec strip_expired_ranges ranges pos =
  begin match ranges with
  | [] -> []
  | hd::tl ->
      if hd.rend > pos then ranges
      else strip_expired_ranges tl pos 
  end

  


let debug_intervals ppf fd =
  Format.fprintf ppf "*** Intervals\n";
  Format.fprintf ppf "%s\n" fd.fun_name;

  let dump_interval i =
      Format.fprintf ppf "  ";
      Printmach.reg ppf i.reg;
      List.iter (fun r ->
	      Format.fprintf ppf " [%d;%d[ " r.rbegin r.rend
	    ) i.ranges;
      Format.fprintf ppf "\n"
  in
  List.iter dump_interval !fixed_interval_list;
  List.iter dump_interval !interval_list;
  ()


let get_and_initialize_interval intervals reg pos_tst pos_set use_kind =
  let interval = intervals.(reg.stamp) in
  if interval.iend = 0 then begin
    interval.ibegin <- pos_tst;
    interval.iend <- pos_set;
    interval.reg <- reg;
    interval.ranges <- [{rbegin = pos_tst; rend = pos_set; }]
  end;
  interval
   

let update_interval_position intervals pos_tst pos_set use_kind reg =
  let interval = get_and_initialize_interval intervals reg pos_tst pos_set use_kind in
  let range = begin match interval.ranges with |[] -> Misc.fatal_error "Illegal empty range" | hd::_ -> hd end in

  interval.iend <- pos_set;

  if (range.rend = pos_tst || (range.rend + 1) = pos_tst) && use_kind != 1 then
    range.rend <- pos_set
  else if range.rbegin = pos_tst && range.rend = pos_tst && use_kind = 1 then
    range.rend <- pos_set
  else 
    interval.ranges <- {rbegin=pos_tst;rend=pos_set;} :: interval.ranges



let update_interval_position_by_reg_array intervals regs pos_tst pos_set use_kind =
  Array.iter (update_interval_position intervals  pos_tst pos_set use_kind) regs
         
let update_interval_position_by_reg_set intervals regs pos_tst pos_set use_kind =
  Set.iter (update_interval_position intervals  pos_tst pos_set use_kind) regs
 
let update_interval_position_by_instr intervals instr pos_tst pos_set =
  update_interval_position_by_reg_array intervals instr.arg pos_tst pos_set 0;
  update_interval_position_by_reg_array intervals instr.res pos_set pos_set 1;
  update_interval_position_by_reg_set intervals instr.live pos_tst pos_set 0


let insert_pos_for_live intervals instr pos = 
  if (not (Set.is_empty instr.live)) || Array.length instr.arg > 0 then
  begin
    pos := succ !pos;
    update_interval_position_by_reg_set intervals instr.live !pos !pos 0;
    update_interval_position_by_reg_array intervals instr.arg !pos !pos 0
  end

let insert_destroyed_at_oper intervals instr pos =
  let destroyed = Proc.destroyed_at_oper instr.desc in
  if Array.length destroyed > 0 then
    update_interval_position_by_reg_array intervals destroyed pos pos 1 

let insert_destroyed_at_raise intervals pos = 
  let destroyed = Proc.destroyed_at_raise in
  if Array.length destroyed > 0 then
    update_interval_position_by_reg_array intervals destroyed pos pos 1


(* generate all intervals.
   the intervals will be expanded by one step at the beginning and
   the ending of a basic block
*)
let build_intervals fundecl =

  let intervals = Array.init (Reg.num_registers()) (fun i ->
    { reg = Reg.dummy;
      ibegin = 0;
      iend = 0;
      ranges = [];
    }) in


  let rec walk_instruction i pos shift =
    pos := !pos + 1 + shift;
    update_interval_position_by_instr intervals i (!pos - shift)  !pos;

    
    begin match i.desc with
    | Iend -> 
        (* end ends a bb *)
        insert_pos_for_live intervals i pos;     

    | Iop(Icall_ind | Icall_imm _ | Iextcall(_, true) | Itailcall_ind | Itailcall_imm _) ->
        walk_instruction i.next pos 0 

    | Iop _ ->
        insert_destroyed_at_oper intervals i !pos;
        walk_instruction i.next pos 0

    | Ireturn ->
        insert_destroyed_at_oper intervals i !pos;
        (* returns ends a bb *)
        insert_pos_for_live intervals i pos;     
        walk_instruction i.next pos 0


    | Iifthenelse(test, ifso, ifnot) ->
        insert_destroyed_at_oper intervals i !pos;
        (* if ends a bb *)
        insert_pos_for_live intervals i pos;

        (* ifso starts a new bb *)
        walk_instruction ifso pos 1;

        (* ifnot starts a new bb *)
        walk_instruction ifnot pos 1;

        (* next starts a new bb *)
        walk_instruction i.next pos 1
    | Iswitch(index, cases) ->
        insert_destroyed_at_oper intervals i !pos;
        (* switch ends a bb *)
        insert_pos_for_live intervals i pos;

        for j = 0 to Array.length cases -1 do
          (* each case starts a new bb *)
          walk_instruction cases.(j) pos 1
        done;
        (* next starts a new bb *)
        walk_instruction i.next pos 1
    | Iloop body ->
        insert_destroyed_at_oper intervals i !pos;
        (* loop ends a bb *)
        insert_pos_for_live intervals i pos;

        (* the body starts a new block *)
        walk_instruction body pos 1;

        (* next starts a new bb *)
        walk_instruction i.next pos 1
    | Icatch(io, body, handler) ->
        insert_destroyed_at_oper intervals i !pos;
        (* catch ends a bb *)
        insert_pos_for_live intervals i pos;

        (* the body starts a new bb *)
        walk_instruction body pos 1;

        (* the handler starts a new bb *)
        walk_instruction handler pos 1;

        (* next starts a new bb *)
        walk_instruction i.next pos 1;
    | Iexit nfail ->
        insert_destroyed_at_oper intervals i !pos;
        (* exit ends a bb *)
        insert_pos_for_live intervals i pos;

    | Itrywith(body, handler) ->
        insert_destroyed_at_oper intervals i !pos;
        (* trywith ends a bb *)
        insert_pos_for_live intervals i pos;

        (* the body starts a new bb *)
        walk_instruction body pos 1;

        (* the handler starts a new bb *)
        insert_pos_for_live intervals handler pos;
        insert_destroyed_at_raise intervals !pos;
        walk_instruction handler pos 0;

        (* nex starts a new bb *)
        walk_instruction i.next pos 1
    | Iraise ->
        (* raise ends a bb *)
        insert_pos_for_live intervals i pos;

        walk_instruction i.next pos 1
    end



  in

  let pos = ref 0 in
  walk_instruction fundecl.fun_body pos 1;


  interval_list := []; 
  fixed_interval_list := []; 
  Array.iter (fun i -> 
        if i.iend != 0 then begin
          i.ranges <- List.rev i.ranges;
          begin match i.reg.loc with
          | Reg r -> fixed_interval_list := i :: !fixed_interval_list
          | _ -> interval_list := i :: !interval_list
          end
        end) intervals;


  interval_list := List.sort (fun i0 i1 -> i0.ibegin - i1.ibegin) !interval_list;

  ()
