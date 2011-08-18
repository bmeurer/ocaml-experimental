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


open Interval
open Clflags
open List
open Format
open Mach


type active_t =
{
    mutable active : interval list;
    mutable inactive : interval list;
    mutable fixed : interval list;
}


let active = Array.init Proc.num_register_classes (fun i -> {active = []; inactive = []; fixed= [] })

let rec insert_into active current = 
  begin match active with
  | [] -> [current]
  | interval::tl ->
    (* check code for <= or < *)
    if interval.iend <= current.iend then 
      current :: active
    else
      interval :: insert_into tl current
  end


let rec release_expired_fixed pos intervals =
  begin match intervals with
  | [] -> []
  | interval::tl ->
      if interval.iend > pos then begin
        interval.ranges <- Interval.strip_expired_ranges interval.ranges pos;
        interval :: release_expired_fixed pos tl
      end
      else
        []
 end

 
let rec release_expired_active active_cl pos intervals =
  begin match intervals with
  | [] -> []
  | interval::tl ->
      if interval.iend > pos then begin
        interval.ranges <- Interval.strip_expired_ranges interval.ranges pos;
        if Interval.live_on interval pos then
          interval :: release_expired_active active_cl pos tl
        else begin
          active_cl.inactive <- insert_into active_cl.inactive interval;
          release_expired_active active_cl pos tl
        end
      end
      else
        []
 end

let rec release_expired_inactive active_cl pos intervals =
  begin match intervals with
  | [] -> []
  | interval::tl ->
      if interval.iend > pos then begin
        interval.ranges <- Interval.strip_expired_ranges interval.ranges pos;
        if not (Interval.live_on interval pos) then 
          interval :: release_expired_inactive active_cl pos tl
        else begin
          active_cl.active <- insert_into active_cl.active interval;
          release_expired_inactive active_cl pos tl
        end
      end
      else
        []
 end


   

let get_stack_slot cl = 
  let nslots = Proc.num_stack_slots.(cl) in
  Proc.num_stack_slots.(cl) <- nslots + 1;
  nslots
    


let pop_active active = 
  begin match active with
  | [] -> []
  | _::tl -> tl
  end
  

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
    let active_cl = active.(cl) in

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

    remove_bound active_cl.active;
      
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
    remove_bound_overlapping active_cl.inactive;
    remove_bound_overlapping active_cl.fixed;
      

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
      active_cl.active <- insert_into active_cl.active interval;
      true
    end;
  end
 

let allocate_blocked_register interval =
  let cl = Proc.register_class interval.reg in
  let active_cl = active.(cl) in
  
  
  if active_cl.active = [] then begin
    (* this is the special case when there are no register at all
       in the register class. This can happen e.g. for float Regs on i386 *)
    interval.reg.Reg.loc <- Reg.Stack(Reg.Local (get_stack_slot cl));
    interval.reg.Reg.spill <- true
  end
  else begin
    
    (* get the latest interval in active *)
    let last_active = List.hd active_cl.active in
    
    if last_active.iend > interval.iend then begin
      (* last interval in active ends latest -> spill it*)
      
      (* transfer the register from the active in the current interval *)
      begin match last_active.reg.Reg.loc with 
      | Reg.Reg r -> interval.reg.Reg.loc <- Reg.Reg r
      | _ -> ()
      end;
      
      (* remove the latest interval from active ... *)
      active_cl.active <- pop_active active_cl.active;
      (* ... and insert the current *)
      active_cl.active <- insert_into active_cl.active interval;
      
      (* now get a new stack slot for the spilled register *)
      last_active.reg.Reg.loc <- Reg.Stack(Reg.Local (get_stack_slot cl));
      last_active.reg.Reg.spill <- true
    end
    else begin
      (* the current interval ends latest -> spill it *)
      interval.reg.Reg.loc <- Reg.Stack(Reg.Local (get_stack_slot cl));
      interval.reg.Reg.spill <- true
    end;
  end;
  ()


let handle_interval interval =
  let position = interval.ibegin in
  
  (* release all intervals that have been expired at the current step*)
  for i = 0 to Proc.num_register_classes - 1 do
    let active_cl = active.(i) in
    active_cl.active    <- release_expired_active active_cl position active_cl.active;
    active_cl.inactive  <- release_expired_inactive active_cl position active_cl.inactive;
    active_cl.fixed     <- release_expired_fixed position active_cl.fixed;
  done;
  
  
  (* find a register for allocation *)
  if not (try_alloc_free_register interval) then 
    (* a valid free register could not be found, so we have to
       decide which interval is to be spilled *)
    allocate_blocked_register interval

(* create active liste for every register class *)
let initialize_interval_lists intervals =

  
  for i=0 to Proc.num_register_classes - 1 do 
    let active_cl = active.(i) in
    (* start with empty actives *)
    active_cl.active    <- [];
    active_cl.inactive  <- [];
    active_cl.fixed     <- [];
  done;

  (* add all fixed intervals to the list of active_fixed intervals *)
  let rec add_fixed_intervals intervals =
    begin match intervals with
    | [] -> ()
    | i :: tl -> 
      let active_cl = active.(Proc.register_class i.reg) in
      active_cl.fixed <- i :: active_cl.fixed;
      add_fixed_intervals tl
    end in
  add_fixed_intervals intervals;

  for i = 0 to Proc.num_register_classes - 1 do
    let active_cl = active.(i) in
    active_cl.fixed <- List.sort (fun i0 i1 -> i1.iend - i0.iend) active_cl.fixed
  done


 
  

let walk_intervals intervals fixed_intervals fd =
  (* Initialize the stack slots *)
  for i = 0 to Proc.num_register_classes - 1 do
    Proc.num_stack_slots.(i) <- 0
  done;
  
  
  (* create the active lists *)
  initialize_interval_lists fixed_intervals;
  

  (* Walk all the intervals within the list *)
  List.iter handle_interval intervals

