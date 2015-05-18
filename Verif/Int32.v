
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
(* Copyright (c) 2011. Greg Morrisett, Gang Tan, Joseph Tassarotti, 
   Jean-Baptiste Tristan, and Edward Gan.

   This file is part of RockSalt.

   This file is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.
*)

Add LoadPath "../Model".
Require Import Tacs.
Require Import List.
Require Import ZArith.
Require Export Psatz.
Require Coqlib.
Require Import Bits.
Export Word.

Local Open Scope Z_scope.

(** * Data structures *)
Require Coq.Sets.Ensembles.
Definition Int8Ensemble := Ensembles.Ensemble int8.
Definition w8add := @Word.add 7.
Definition w8sub := @Word.sub 7.
Definition w8neg := @Word.neg 7.
Notation w8modulus := (modulus 7).

(** * Abbreviations *)
Infix "+8" := w8add (at level 50, left associativity).
Infix "+8" := w8add (at level 50, left associativity).
Notation "i +8_z z" := (i +8 (repr z))
  (at level 50, left associativity).
Notation "i +8_p p" := (i +8 (repr (Zpos p)))
  (at level 50, left associativity).
Notation "i +8_n n" := (i +8 (repr (Z_of_nat n)))
  (at level 50, left associativity).

Infix "-8" := w8sub (at level 50, left associativity).
Notation "i -8_z z" := (i -8 (repr z))
  (at level 50, left associativity).
Notation "i -8_p p" := (i -8 (repr (Zpos p)))
  (at level 50, left associativity).
Notation "i -8_n n" := (i -8 (repr (Z_of_nat n)))
  (at level 50, left associativity).

Notation "-8" := w8neg (at level 35, right associativity).

Notation int8_zero := (@Word.zero 7).
(*Notation int8_max := (@repr 7 (Word.max_unsigned 7))*)
Notation int8_max := (@Word.mone 7).
Notation int8_of_nat n := (@repr 7 (Z_of_nat n)).

Definition int8_ltu_bool := @Word.ltu 7.
Definition int8_eq_bool := @Word.eq 7.
Definition int8_lequ_bool := @Word.lequ 7.
Definition int8_gtu_bool i1 i2 := (int8_ltu_bool i2 i1).
Definition int8_gequ_bool i1 i2 := (int8_lequ_bool i2 i1).

Notation "i1 =8 i2" := (int8_eq_bool i1 i2 = true) (at level 70).
Notation "i1 <>8 i2" := (int8_eq_bool i1 i2 = false) (at level 70).
Notation "i1 <8 i2" := (int8_ltu_bool i1 i2 = true) (at level 70).
Notation "i1 <=8 i2" := (int8_lequ_bool i1 i2 = true) (at level 70).
Notation "i1 >8 i2" := (int8_gtu_bool i1 i2 = true) (at level 70).
Notation "i1 >=8 i2" := (int8_gequ_bool i1 i2 = true) (at level 70).

(** * Basic lemmas *)

Lemma add8_zero_r : forall i, i +8_n 0 = i.
Proof. simpl. apply add_zero. Qed.

Lemma int8_modulus_constant:
  w8modulus = 256.
Proof. unfold modulus. unfold Word.wordsize.
  trivial.
Qed.

Lemma int8_eq_rewrite :
  forall i1 i2, i1 = i2 -> i1 =8 i2.
Proof. apply int_eq_true_iff2. Qed.

Lemma int8_neq_rewrite :
  forall i1 i2, i1 <> i2 -> i1 <>8 i2.
Proof. apply int_eq_false_iff2. Qed.

Lemma int8_minus_rewrite : forall x y,
  unsigned x >= unsigned y -> unsigned (x -8 y) = unsigned x - unsigned y.
Proof. intros. unfold w8sub, sub. rewrite unsigned_repr2. trivial. 
  generalize (unsigned_range x), (unsigned_range y). lia.
Qed.

Remark Zmod_plus_eq_self : forall a b c, (a + b) mod c = a mod c -> b mod c = 0.
Proof. intros.
  assert (b = (a+b-a)) as H2 by ring.
  rewrite H2. rewrite Zminus_mod. rewrite H. rewrite Zminus_diag.
  apply Zmod_0_l.
Qed.

Lemma int8_plus_eq_zero : forall x y, x = x +8 y -> y = int8_zero.
Proof. intros x y Hc.
  destruct x as [xv Hx]. destruct y as [yv Hy].
  unfold Word.add, repr in Hc. simpl in Hc.
  injection Hc. intro H4.
  apply mkint_eq.
  assert (xv = xv mod w8modulus) as H6. 
    apply eq_sym. apply Zmod_small. assumption.
  rewrite H6 in H4 at 1.
  apply eq_sym in H4. apply Zmod_plus_eq_self in H4.
  rewrite Zmod_small in H4 by assumption. rewrite H4.
  rewrite Zmod_0_l. trivial.
Qed.

(** ** Tactics for int8 *)

(** Convert operations on int8 to operations on Z *)

(* converting x=y to unsigned x = unsigned y, when x and y are of type int8 *)
Ltac elim_int8_eq := 
  repeat match goal with
    | [H: ?X = ?Y |- _] =>
      match type of X with
        | int 7 => assert (unsigned X = unsigned Y) by congruence; clear H
        | _ => idtac
      end
  end.

Ltac int8_to_Z_tac :=  
  unfold int8_gtu_bool, int8_gequ_bool, 
    int8_lequ_bool, int8_ltu_bool, int8_eq_bool in *;
  autorewrite with int_to_Z in *; 
  elim_int8_eq.

(** convert nat to Z *)
Hint Rewrite inj_plus inj_mult : nat_to_Z.
Hint Rewrite inj_minus1 using omega : nat_to_Z.
Hint Rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P : nat_to_Z.

Lemma Z_of_nat_0 : Z_of_nat 0%nat = 0. trivial. Qed.
Lemma Z_of_nat_1 : Z_of_nat 1%nat = 1. trivial. Qed.
Hint Rewrite Z_of_nat_0 Z_of_nat_1 : nat_to_Z.

Lemma inj_S2 : forall n, (Z_of_nat (S n) = Z_of_nat n + 1).
Proof. intros. apply inj_S. Qed.
Hint Rewrite inj_S2 : nat_to_Z.

Hint Rewrite inj_Zabs_nat : nat_to_Z.
Hint Rewrite Zabs_eq using lia : nat_to_Z.

(* Converting hypothesis about nats to Z:
     * n1 = n2 ===> Z_of_nat n1 = Z_of_nat n2
     * n1 > n2 ===> Z_of_nat n1 > Z_of_nat n2
     * ...  
   This would not be necessary if we used omega instead of lia.
   Since lia cannot mix facts of Z and nat, we have to
   convert every equality and inquality between nat to Z;
   we also have to add hypothesis (Z_of_nat n >=0) for every
   nat n.
*)
Ltac nat_hyp_to_Z_tac :=
  repeat match goal with
           | [H : ?X = ?Y |- _] =>
             match type of X with
               | nat => apply inj_eq in H
               | _ => fail 1
             end
           | [H: le ?X ?Y |- _] =>  apply inj_le in H
           | [H: Peano.gt ?X ?Y |- _] =>  apply inj_gt in H
           | [H: ge ?X ?Y |- _] =>  apply inj_ge in H
           | [H: Peano.lt ?X ?Y |- _] =>  apply inj_lt in H
           | [n: nat |- _] => extend (Zle_0_nat n)
         end.

(* need to repeat autorewrite below because rewritng rules such as inj_minus1 might
   depend on the results of other rewriting rules so that omega will succeed *)
Ltac nat_to_Z_tac :=  nat_hyp_to_Z_tac; repeat autorewrite with nat_to_Z in *.
Ltac nat_to_Z_in_goal :=  autorewrite with nat_to_Z.
Ltac nat_to_Z_in H :=  autorewrite with nat_to_Z in H.

(** convert Z to nat *)
Hint Rewrite <- inj_plus inj_mult: Z_to_nat.
Hint Rewrite <- inj_minus1 using omega : Z_to_nat.
Hint Rewrite <- Z_of_nat_0 Z_of_nat_1 : Z_to_nat.

Ltac Z_to_nat_in_goal := autorewrite with Z_to_nat.
Ltac Z_to_nat_in H := autorewrite with Z_to_nat in H.
  
(** * Definition and properties of noOverflow *)
Definition addZ_list (l:list int8) : Z := 
  List.fold_right (fun (a:int8) (z:Z) => unsigned a + z) 0 l.

(** A semantic definition that adding a list of int8s does not overflow *)
Definition noOverflow (l:list int8) : Prop := addZ_list l < w8modulus.

Ltac noOverflow_simpl := 
  unfold noOverflow; cbv [addZ_list List.fold_right].
Ltac noOverflow_simpl_in H :=
  unfold noOverflow in H; cbv [addZ_list List.fold_right] in H.

(** Check a +8 b does not overflow; it is equivalent to a + b < 2^8 
    and also equivalent to a +8 b = a + b; this formulation is easy to 
    convert to checks in real programs. *)
Definition checkNoOverflow (a b:int8) : bool :=
  int8_lequ_bool a (a +8 b).

(** ** Properties of noOverflow *)
Lemma checkNoOverflow_equiv_noOverflow : forall a b,
  checkNoOverflow a b = true <-> noOverflow (a :: b :: nil).
Proof. intros; generalize (unsigned_range a), (unsigned_range b); 
  intros Ha Hb; unfold checkNoOverflow, noOverflow; split.
  intros. int8_to_Z_tac. simpl. rewrite Zplus_0_r.
    apply Znot_ge_lt; intro Hc.
    unfold "+8", repr in H. simpl in H.
    assert ((unsigned a + unsigned b) mod w8modulus = 
              unsigned a + unsigned b - w8modulus) as H5.
      apply Coqlib.Zmod_unique with (a:=1) ; lia.
    rewrite H5 in H. lia.
  intros. simpl in H. rewrite Zplus_0_r in H.
    int8_to_Z_tac. unfold "+8", repr. simpl.
    assert (0 <= unsigned a + unsigned b < w8modulus) by lia.
    rewrite (Zmod_small _ _ H0). lia.
Qed.

Lemma noOverflow_2_iff : forall a b, 
  noOverflow (a::b::nil) <-> unsigned (a +8 b) = unsigned a + unsigned b.
Proof. intros; generalize (unsigned_range a), (unsigned_range b); 
  intros Ha Hb; unfold noOverflow; split; unfold "+8", repr; simpl.
  intros. apply Zmod_small. simpl in H.
    lia.
  intros. 
    assert (0 <= unsigned a + unsigned b < w8modulus).
      rewrite <- H; apply Z_mod_lt. apply Word.modulus_pos.
    lia.
Qed.

Lemma int8_add_rewrite : forall (a b:int8),
  unsigned a + unsigned b < w8modulus
    -> unsigned (a +8 b) = unsigned a + unsigned b.
Proof. intros. unfold "+8", repr. simpl.
  generalize (unsigned_range a) (unsigned_range b); intros.
  rewrite Zmod_small by lia. trivial.
Qed.

(** ** Tactics for noOverflow *)

(** Eliminate checkNoOverflow *)
Ltac checkNoOverflow_elim :=
  repeat match goal with
           | [H: checkNoOverflow _ _ = true |- _] =>
             apply checkNoOverflow_equiv_noOverflow in H
           | [ |- checkNoOverflow _ _ = true] =>
             apply checkNoOverflow_equiv_noOverflow
         end.

(* For any occurence of "unsigned x" in the context, add the 
   assumption (0 <= unsigned x < 2^8)*)
Ltac add_unsigned_rng_tac :=
  repeat match goal with
           | [H:context[unsigned ?X] |- _] =>
             extend (unsigned_range X)
         end.

(* converting everything to Z so that lia can be used. *)

Require RTL.

Ltac pos_to_Z_tac := autorewrite with pos_to_Z_db in *.

Hint Rewrite Zpos_plus_distr : pos_to_Z_db.


Ltac all_to_Z_tac :=
  unfold noOverflow in *; cbv [addZ_list List.fold_right] in *;
  int8_to_Z_tac; add_unsigned_rng_tac; nat_to_Z_tac; pos_to_Z_tac;
  unfold RTL.size8 in *.

Ltac int8_simplify := all_to_Z_tac; repeat autorewrite with int8_simpl_db in *.
Ltac int8_prover := int8_simplify; lia.

Ltac int8_simplify_in_goal := 
  nat_to_Z_in_goal; autorewrite with int8_simpl_db.
Ltac int8_simplify_in H := 
  nat_to_Z_in H; autorewrite with int8_simpl_db in H.

(** A rewrite tactic that
    (1) rewrites to (unsigned a + unsigned b) when
        (unsigned a + unsigned b < 2^8 holds
    (3) rewrites unsigned (repr z) to z when 0 <= z < 2^8 *)
Hint Rewrite int8_add_rewrite using (lia || (int8_simplify_in_goal; lia))
  : int8_simpl_db.
Hint Rewrite int8_minus_rewrite using lia : int8_simpl_db.
Hint Rewrite Word.unsigned_repr2 using lia : int8_simpl_db.

(** ** More lemmas about noOverflow *)
Lemma checkNoOverflow_3_sound : forall (a b c:int8),
  checkNoOverflow a b = true -> checkNoOverflow (a +8 b) c = true
    -> noOverflow (a::b::c::nil).
Proof. intros. checkNoOverflow_elim. int8_prover. Qed.

(** * addrRegion *)

Definition addrRegion (start limit:int8):Int8Ensemble :=
  fun x:int8 => exists i:int8, x = start +8 i /\ i <=8 limit.

Lemma addrRegion_start_in : forall start limit, 
  Ensembles.In _ (addrRegion start limit) start.
Proof. autounfold with sets. intros.
  unfold addrRegion.
  exists int8_zero. 
  split. rewrite add8_zero_r. trivial.
  apply Word.int_lequ_zero.
Qed.

(** * disjointRegions *)
(** Check region [start1, start1+limit1] is disjoint from 
    [start2, start2+limit2]; For simplicity, neither region can wrap
    around the 8-bit address space. *)
Definition disjointRegions (start1 limit1 start2 limit2:int8) : bool :=
  (int8_ltu_bool (start1 +8 limit1) start2 ||
   int8_ltu_bool (start2 +8 limit2) start1)%bool.

Lemma disjointRegions_sound :
  forall (s1 l1 s2 l2:int8),
    checkNoOverflow s1 l1 = true 
      -> checkNoOverflow s2 l2 = true
      -> disjointRegions s1 l1 s2 l2 = true 
      -> Ensembles.Disjoint _ (addrRegion s1 l1) (addrRegion s2 l2).
Proof. intros. split; intros. autounfold with sets. intro Hc. 
  destruct Hc as [x [i1 [H10 H11]] [i2 [H12 H13]]].
  unfold disjointRegions in H1.
  checkNoOverflow_elim.
  rewrite H10 in H12; clear H10.
  bool_elim_tac; int8_prover.
Qed.

(** * Some properties about ensembles *)
(* not sure where to put these lemmas *)
Lemma included_disjoint : forall A r1 r2 r3,
  Ensembles.Included A r1 r2 -> Ensembles.Disjoint A r2 r3
    -> Ensembles.Disjoint A r1 r3.
Proof. intros. destruct H0. split.
  autounfold with sets in *. intros. intro Hc.
  apply (H0 x).
  destruct Hc. split; auto with sets.
Qed.

Lemma included_trans : forall A r1 r2 r3,
  Ensembles.Included A r1 r2 -> Ensembles.Included A r2 r3
    -> Ensembles.Included A r1 r3.
Proof. auto with sets. Qed.

