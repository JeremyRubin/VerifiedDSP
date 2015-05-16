

Require Import String.
Require Import Ascii.
Require Import List.
Require Import ListSet.
Require Import EqNat.
Import ListNotations.
Require Import Arith.
Open Scope list_scope.
Fixpoint len {T:Type}(x : list T) : nat :=
  match x with
    | x::b => 1+len b
    | nil => 0
  end.
Fixpoint suml (x : list nat) : nat :=
  match x with
    | x::b => x+suml b
    | nil => 0
  end.