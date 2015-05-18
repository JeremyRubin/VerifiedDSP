
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
Import ListNotations.
Require Import Arith.
Open Scope list_scope.
Require Import IOModule.


Require Import Wiring.

Module Wires := Wiring.Wiring(IO).

Module IORUN.
  Import Wires.


  Definition pin_trace_gen w : list (nat* list IO.t):= map (fun p => (p, nil)) (pins w).
  Search option.
  Fixpoint find_trace p pt  : option (list IO.t) :=
    match pt with 
      | [] => None
      | (p', t)::rest => if beq_nat p' p then Some t else find_trace p rest 
    end.
  Definition find_traces (p :list nat) (pt : list (nat * list IO.t))  : option (list (list IO.t)) :=
    let elts :=map (fun f =>  (find_trace f pt))  p in
    let none := forallb (fun x => match x with | None => false | _ => true end ) elts in
    if none then 
      Some (map (fun f =>  match f with | None => [] | Some x => x end) elts)
    else None.

  Definition any_trace  (pt : list (nat * list IO.t) ): list IO.t :=
    match pt with 
      | nil => nil
      | (p', t)::rest => t
    end.
  Fixpoint update_trace pt u acc:=
    match u with
      | (p, iot)::rest =>
        match find_trace p pt with
          | None => update_trace pt rest acc
          | Some trace =>
            update_trace pt rest ((p, iot::trace)::acc)
        end
      | [] => acc
    end.
  Print IO.func.
  Fixpoint step' w pt (u : list (nat * IO.t))  :=
    let add_i := set_add in 
    match w with 
      | base  =>
        update_trace pt (u) nil
      | watch_set w' from (IO.fn_args n fn) to =>
        let o_traces := (find_traces from pt) in
        match o_traces with
          | None => pt
          | Some traces =>
            step' w' pt ((to, fn traces )::u)
        end
      |  just_set w' (IO.fn_args n fn) to =>
         step' w' pt  ((to, fn [any_trace  pt ])::u)
      | join w1 w2 =>
        app (step' w2 pt [])  (step' w1 pt u)
      | doc w' _ _ => step' w' pt u
    end.
  Definition step w :=
    step' w (pin_trace_gen w) [].

  Fixpoint run' (w:wiring) (pt: list (nat * list IO.t)) fuel  :=
    match fuel with
      | O => pt
      | S n => run' w (step' w pt []) n
    end.
  Definition run w fuel :=
    run' w (pin_trace_gen w) fuel.
End IORUN.