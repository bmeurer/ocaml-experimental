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

let interval_list = ref ([] : t list)
let fixed_interval_list = ref ([] : t list)
let all_intervals() = !interval_list
let all_fixed_intervals() = !fixed_interval_list

(* Check if two intervals overlap *)

let overlap i0 i1 =
  let rec overlap_ranges rl0 rl1 =
    match rl0, rl1 with
      r0 :: rl0', r1 :: rl1' ->
        if r0.rend > r1.rbegin && r1.rend > r0.rbegin then true
        else if r0.rend < r1.rend then overlap_ranges rl0' rl1
        else if r0.rend > r1.rend then overlap_ranges rl0 rl1'
        else overlap_ranges rl0' rl1'
    | _ -> false in
  overlap_ranges i0.ranges i1.ranges

let is_live i pos =
  let rec is_live_in_ranges = function
    [] -> false
  | r :: rl -> if pos < r.rbegin then false
               else if pos < r.rend then true
               else is_live_in_ranges rl in
  is_live_in_ranges i.ranges

let remove_expired_ranges i pos =
  let rec filter = function
    [] -> []
  | r :: rl' as rl -> if pos < r.rend then rl
               else filter rl' in
  i.ranges <- filter i.ranges

let update_interval_position intervals pos_tst pos_set use_kind reg =
  let i = intervals.(reg.stamp) in
  if i.iend == 0 then begin
    i.ibegin <- pos_tst;
    i.iend <- pos_set;
    i.reg <- reg;
    i.ranges <- [{rbegin = pos_tst; rend = pos_set}]
  end;
  match i.ranges with
    [] ->
      Misc.fatal_error "Illegal empty range"
  | range :: _ ->
      i.iend <- pos_set;
      if (range.rend == pos_tst || (range.rend + 1) == pos_tst) && use_kind != 1 then
        range.rend <- pos_set
      else if range.rbegin == pos_tst && range.rend == pos_tst && use_kind == 1 then
        range.rend <- pos_set
      else
        i.ranges <- {rbegin = pos_tst; rend = pos_set} :: i.ranges

let update_interval_position_by_array intervals regs pos_tst pos_set use_kind =
  Array.iter (update_interval_position intervals pos_tst pos_set use_kind) regs
         
let update_interval_position_by_set intervals regs pos_tst pos_set use_kind =
  Set.iter (update_interval_position intervals pos_tst pos_set use_kind) regs
 
let update_interval_position_by_instr intervals instr pos_tst pos_set =
  update_interval_position_by_array intervals instr.arg pos_tst pos_set 0;
  update_interval_position_by_array intervals instr.res pos_set pos_set 1;
  update_interval_position_by_set intervals instr.live pos_tst pos_set 0

let insert_pos_for_live intervals instr pos =
  if (not (Set.is_empty instr.live)) || Array.length instr.arg > 0 then
  begin
    pos := succ !pos;
    update_interval_position_by_set intervals instr.live !pos !pos 0;
    update_interval_position_by_array intervals instr.arg !pos !pos 0
  end

let insert_destroyed_at_oper intervals instr pos =
  let destroyed = Proc.destroyed_at_oper instr.desc in
  if Array.length destroyed > 0 then
    update_interval_position_by_array intervals destroyed pos pos 1 

let insert_destroyed_at_raise intervals pos =
  let destroyed = Proc.destroyed_at_raise in
  if Array.length destroyed > 0 then
    update_interval_position_by_array intervals destroyed pos pos 1

(* Build all intervals.
   The intervals will be expanded by one step at the start and end
   of a basic block. *)

let build_intervals fd =
  let intervals = Array.init
                    (Reg.num_registers())
                    (fun _ -> {
                      reg = Reg.dummy;
                      ibegin = 0;
                      iend = 0;
                      ranges = []; }) in
  let pos = ref 0 in
  let rec walk_instruction i shift =
    pos := !pos + 1 + shift;
    update_interval_position_by_instr intervals i (!pos - shift) !pos;
    begin match i.desc with
      Iend ->
        (* Iend ends a basic block *)
        insert_pos_for_live intervals i pos
    | Iop(Icall_ind | Icall_imm _ | Iextcall(_, true)
          | Itailcall_ind | Itailcall_imm _) ->
        walk_instruction i.next 0
    | Iop _ ->
        insert_destroyed_at_oper intervals i !pos;
        walk_instruction i.next 0
    | Ireturn ->
        insert_destroyed_at_oper intervals i !pos;
        (* Ireturn ends a basic block *)
        insert_pos_for_live intervals i pos;     
        walk_instruction i.next 0
    | Iifthenelse(_, ifso, ifnot) ->
        insert_destroyed_at_oper intervals i !pos;
        (* Iifthenelse ends a basic block *)
        insert_pos_for_live intervals i pos;
        (* ifso starts a new basic block *)
        walk_instruction ifso 1;
        (* ifnot starts a new basic block *)
        walk_instruction ifnot 1;
        (* next starts a new basic block *)
        walk_instruction i.next 1
    | Iswitch(_, cases) ->
        insert_destroyed_at_oper intervals i !pos;
        (* Iswitch ends a basic block *)
        insert_pos_for_live intervals i pos;
        (* Each case starts a new basic block *)
        Array.iter (fun case -> walk_instruction case 1) cases;
        (* next starts a new basic block *)
        walk_instruction i.next 1
    | Iloop body ->
        insert_destroyed_at_oper intervals i !pos;
        (* Iloop ends a basic block *)
        insert_pos_for_live intervals i pos;
        (* body starts a new basic block *)
        walk_instruction body 1;
        (* next starts a new basic block *)
        walk_instruction i.next 1
    | Icatch(_, body, handler) ->
        insert_destroyed_at_oper intervals i !pos;
        (* Icatch ends a basic block *)
        insert_pos_for_live intervals i pos;
        (* body starts a new basic block *)
        walk_instruction body 1;
        (* handler starts a new basic block *)
        walk_instruction handler 1;
        (* next starts a new basic block *)
        walk_instruction i.next 1
    | Iexit _ ->
        insert_destroyed_at_oper intervals i !pos;
        (* Iexit ends a basic block *)
        insert_pos_for_live intervals i pos
    | Itrywith(body, handler) ->
        insert_destroyed_at_oper intervals i !pos;
        (* Itrywith ends a basic block *)
        insert_pos_for_live intervals i pos;
        (* body starts a new basic block *)
        walk_instruction body 1;
        (* handler starts a new basic block *)
        insert_pos_for_live intervals handler pos;
        insert_destroyed_at_raise intervals !pos;
        walk_instruction handler 0;
        (* nex starts a new basic block *)
        walk_instruction i.next 1
    | Iraise ->
        (* Iraise ends a basic block *)
        insert_pos_for_live intervals i pos;
        (* next starts a new basic block *)
        walk_instruction i.next 1
    end in
  walk_instruction fd.fun_body 1;
  (* Generate the interval and fixed interval lists *)
  interval_list := []; 
  fixed_interval_list := []; 
  Array.iter
    (fun i -> 
      if i.iend != 0 then begin
        i.ranges <- List.rev i.ranges;
        begin match i.reg.loc with
          Reg _ ->
            fixed_interval_list := i :: !fixed_interval_list
        | _ ->
            interval_list := i :: !interval_list
        end
      end)
    intervals;
  (* Sort the intervals according to their start position *)
  interval_list := List.sort (fun i0 i1 -> i0.ibegin - i1.ibegin) !interval_list
