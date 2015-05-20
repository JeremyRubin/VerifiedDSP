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
Open Scope string_scope.
Add LoadPath "../Model".

Require Import Common.
Require Import IOModule.
Require Import Run.
Import IORUN.
Import Wires.
Require Import c8051.
Import i8051_Component.

Module BB.
  (* Module Integrator_Spec. *)
  (*   Definition io (x:list IO.t):IO.t := suml x. *)
  (* End Integrator_Spec. *)
  (* Module Incrementor_Spec. *)
  (*   Definition io (x:list IO.t):IO.t := len x. *)
  (* End Incrementor_Spec. *)


  Fixpoint alt x start:=
    match x with
      | O => start
      | S n => alt n (if beq_nat start 0 then 1 else 0)
    end.
  (* Module Alternator_Spec. *)
  (*   Require Import Arith.Even. *)
  (*   Definition io (x:list IO.t):IO.t := alt (length x) 1. *)
  (* End Alternator_Spec. *)

  (* Module Integrator := Component(IO)(Integrator_Spec). *)
  (* Module Incrementor := Component(IO)(Incrementor_Spec). *)
  (* Module Alternator := Component(IO)(Alternator_Spec). *)


  Definition integrator  : IO.func := IO.fn_args 1 (fun x =>suml (hd [] x)).
  Definition incrementor :IO.func := IO.fn_args 1
                                                (fun x =>len (hd [] x)).
  Definition alternator : IO.func :=IO.fn_args 1
                                               (fun x =>
                                                  alt (length (hd [] x)) 1).
  Definition zero_rail   : IO.func := IO.fn_args 0 (fun _ =>0).

  Definition delay_n n default : IO.func := IO.fn_args 1
                                                       (fun x => nth n (hd [] x) default).


  Open Scope wiring_scope.

  Definition demo1 := [] */  zero_rail ~> 0
                           //  [5] ~> integrator~> 6
                           // [2] ~> integrator~> 3
                           */ incrementor ~> 2
                           */ IO.fn_args 0 (fun _=> 10) ~> 5
                           */ alternator ~> 8
                           # 3 "Integrated incrementor"
                           # 3 "Integrated incrementor".

  Compute (docstring demo1).
  Definition demo2 := [] */integrator ~> 9
                           // [6] ~> delay_n 5 0 ~> 10.




  Definition demo3 bin threshold  :=
    [] // (seq 0 32) ~> i8051_Component bin threshold dac ~> 32
         ~&~
         [] */ zero_rail ~> 0
         */ zero_rail ~> 1
         */ zero_rail ~> 2
         */ zero_rail ~> 3
         */ zero_rail ~> 4
         */ zero_rail ~> 5
         */ zero_rail ~> 6
         */ zero_rail ~> 7
         */ zero_rail ~> 8
         */ zero_rail ~> 9
         */ zero_rail ~> 10
         */ zero_rail ~> 11
         */ zero_rail ~> 12
         */ zero_rail ~> 13
         */ zero_rail ~> 14
         */ zero_rail ~> 15
         */ zero_rail ~> 16
         */ zero_rail ~> 17
         */ zero_rail ~> 18
         */ zero_rail ~> 19
         */ zero_rail ~> 20
         */ zero_rail ~> 21
         */ zero_rail ~> 22
         */ zero_rail ~> 23
         */ zero_rail ~> 24
         */ zero_rail ~> 25
         */ zero_rail ~> 26
         */ zero_rail ~> 27
         */ zero_rail ~> 28
         */ zero_rail ~> 29
         */ zero_rail ~> 30
         */ zero_rail ~> 31 .

  Definition run := run.

  Lemma valid_demo3: valid_wiring (demo3 [0] 6).
    admit. (* THis works just slowly *)
    (* autowire. *)

  Qed.
End BB.