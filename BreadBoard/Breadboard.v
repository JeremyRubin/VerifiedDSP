Require Import String.
Require Import Ascii.
Require Import List.
Require Import ListSet.
Require Import EqNat.
Import ListNotations.
Require Import Arith.
Open Scope list_scope.
Open Scope string_scope.

(* Notation "$ x" := (fun f => f x) (at level 0, right associativity, only parsing). *)
(* Notation "f $ x .. y" := (.. (f x) .. y) (at level 0, right associativity, only parsing). *)
Require Import Common.
Require Import IOModule.
Require Import Run.
Import IORUN.
Import Wires.


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

Definition demo1 := base */  zero_rail ~> 0
                         //  [5] ~> integrator~> 6
                         // [2] ~> integrator~> 3
                         */ incrementor ~> 2
                         */ IO.fn_args 0 (fun _=> 10) ~> 5
                         */ alternator ~> 8
                         # 2 "com".
Compute (docstring demo1).
Definition demo2 := base */integrator ~> 9
                         // [6] ~> delay_n 5 0 ~> 10.


