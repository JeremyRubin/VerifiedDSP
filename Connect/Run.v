
(**
    VerifiedDSP
    Copyright (C) {2015}  {Jeremy L Rubin}

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License along
    with this program; if not, write to the Free Software Foundation, Inc.,
    51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.

**)

Require Import String.
Require Import Ascii.
Require Import List.
Require Import ListSet.
Require Import EqNat.
Require Import Arith.
Open Scope list_scope.
Require Import IOModule.

Require Import Vector.
Import Vector.
Import VectorNotations.


Require Import Wiring.

Import Wires.

Module IORUN.
  Import Wires.


  Definition find_trace {c n :nat}  (p:pin) (pt: pintrace n c )  : option (IO.trace c) :=
    match lt_dec p n with
      | left pf => nth pt (Fin.of_nat_lt  pf)
      | right r=> None
    end.
  
  
  Definition find_traces {c n pn:nat} (p :Vector.t _ pn) (pt :pintrace n c)
  : Vector.t (option (IO.trace c)) pn:=
    Vector.map (fun f =>  (find_trace f pt))  p.

  Fixpoint any_trace {c n:nat}  (pt : pintrace n c ): IO.trace c:=
    match pt with 
      | [] => Vector.const 0 c
      | None::rest => any_trace rest
      | Some  t::rest => t
    end.
  Definition find_update {n:nat}  (p:pin) (u: pinupdate n)  : option (IO.t) :=
    match lt_dec p n with
      | left pf => nth u (Fin.of_nat_lt  pf)
      | right r=> None
    end.


  Definition defhd {A n} (d: A) (v:Vector.t A n):=
    match v with
      | v'::_ => v'
      | [] => d
    end.
    Check (andb).
    Check @fold_left.
  Definition sequenceOpt {T c} (m: Vector.t (option T) c) def :=
    let allg := fold_left (fun p v => andb p match v with Some _ => true | None => false end) true m in
    if  allg then
      Some (map (fun f =>
                   match f  with
                     | Some t => t
                     | None => def
                end) m) 
      else None.
      
    (* fix seqOpt {n m} (mv: Vector.t (option T) (S m)) : Vector.t T (n) := *)
    (* match mv with *)
    (*   | None ::_ => None *)
    (*   | Some x::r::s => @seqOpt _ _ (x::acc) (r::s) *)
    (*   | [Some x] => Some (acc) *)
    (*   | [] => Some acc *)
    (* end. *)
  Definition update_trace {c n : nat}
             (pt:pintrace n c)
             (u: pinupdate n) :
    pintrace n (S c) :=
    map2 (fun (pv:(option (IO.trace c))) up =>
           match pv , up with
               | Some t, Some update=> Some ( update ::t)
               | Some t, None => Some ((defhd 0 t)::t)
               | None, _ => None 
           end
             )pt u.

  Require Import Vector.
  Check (Fin.of_nat 10 1).
  Check find_traces.
  Check (IO.trace).
  Fixpoint next_value {c n} (pt: pintrace n c)  w  :=
    
    match w with 
      | watch_set n from fn to =>
        match sequenceOpt (find_traces from pt) (Vector.const 0 c) with
          | None => None
          | Some traces =>
           Some (fn  c traces)
        end
      |  just_set  fn to =>
         Some (fn c [ (any_trace pt)])
      | doc _ _ => None
    end.
  
  Fixpoint vseq (from to:nat) :=
    match to with
      | O => []
      | S n => ( from) ::vseq (S from) n
    end.
  Compute (vseq 0 1).
Fixpoint findf {n} w p : option (component) := match w with
                        | a :: r =>
                          match a with
                            | just_set _ to as c
                            | watch_set _ _ _ to as c=>
                                                if beq_nat to p then
                                                  Some c
                                                else
                                                  findf r p
                            | doc _ _ => findf r p
                          end
                        | [] => None
                      end.
  Definition canonical_wiring := fun n => Vector.t (option component ) n.
  Definition step {c n} {fns: canonical_wiring n} (pt :pintrace n c) :=
    let res := Vector.map (fun f => match f with Some c => next_value pt c | None => None end)  fns in
  update_trace pt res.


  Definition pin_trace_gen   {n} {fns: canonical_wiring n} :
    Vector.t (option (IO.trace 0)) n
    :=
    Vector.map (fun p => match p with | None => None | _ =>Some [] end ) fns.

  Require Import Common.
  Definition canonicalize_wiring {n} (w:wiring (S n)) :
    canonical_wiring (fold_left max 0 (pins w)) :=
    let p := (pins w) in
    let m := Vector.fold_left max 0 p in
    let pindex := vseq 0 m in 
     map (findf w) pindex.

  Fixpoint run' {n} (fns: canonical_wiring n) fuel :=
    match fuel with
        | S f => @step _ n fns (run' fns f)
        | O =>  @pin_trace_gen n fns
    end.
  
  Definition run {n} (w:wiring (S n)) fuel :=
    let fns := canonicalize_wiring w in
    run' fns fuel.

End IORUN.