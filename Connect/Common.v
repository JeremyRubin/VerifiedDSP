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
Require Import EqNat.
Require Import Arith.

Require Import Vector.
Import Vector.
Import VectorNotations.
Definition len {n} {T:Type}(x : Vector.t T n) : nat := n.
Fixpoint suml {n} (x : Vector.t nat n) : nat :=
  match x with
    | x::b => x+suml b
    | nil => 0
  end.

  Fixpoint remove_none {c} {T: Type} (l:Vector.t (option T) c) :=
    match l with
        | [] => List.nil
        | l'::l'' => match l' with
                       | Some v => List.cons v (remove_none  l'')
                       | None => remove_none  l''
                     end
    end.

  Lemma seq_dec : forall {A n} (m : t (option A) n),  {Forall (fun f =>  f <> None) m}  +  {Exists (fun f => f = None) m}.
  
  Proof.
    intros.
    induction m.
    +
      constructor.
      constructor.
    +
      elim (IHm).
    -
      destruct  h.
      *
        intros.
        left.
        apply Forall_cons with (x:=Some a).
        {
          unfold not.
          intros.
          inversion H.
        }
        {
          apply a0.
        }
      *
        intros.
         right.
         apply Exists_cons_hd.
         reflexivity.
    -
      intros.
      destruct  h.
      *
        intros.
        right.
        apply Exists_cons_tl with (x:=Some a).
        apply b.
      *
        right.
        apply Exists_cons_hd .
        reflexivity.
  Defined.

  Fixpoint vseq (from to:nat) :=
    match to with
      | O => []
      | S n => ( from) ::vseq (S from) n
    end.