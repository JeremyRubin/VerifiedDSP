
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
Require Import Vector.
Import VectorNotations.
Open Scope vector_scope.

Require Import IOModule.
Require Import Common.

Require Import Vector.
Import Vector.
Module Wires.
  Definition pin := nat.
  Definition pintrace := fun n c => Vector.t (option (IO.trace c)) n.
  Definition pinupdate := fun n => Vector.t (option IO.t) n.
  Inductive component :=
  | watch_set :   forall {n}, Vector.t pin n -> IO.func n -> pin->  component
  | just_set : IO.func 1 -> pin -> component
  | doc :  pin -> string -> component.
  Definition wiring := fun c => Vector.t component c.
  Notation  "w // m ~> f ~>  n" := ((watch_set m f n) :: w) (at level 80, m at next level) : wiring_scope. 
  Notation  "w */  f ~>  n" := ((just_set f n) :: w) (at level 80, m at next level): wiring_scope. 
  Notation "w1 ~&~ w2" := (Vector.append w1 w2) (at level 80) : wiring_scope.
  Notation "w # p c " := ((doc p c)::w) (at level 80, p at level 0) : wiring_scope.
  Open Scope wiring_scope.

  Open Scope string_scope.
  Fixpoint docstring' {c} (l:wiring c) acc :=
    match l with
      | [] => acc
      | w::w' => 
        match w with
          | watch_set n from fn to => docstring' w' acc
          | just_set  fn to =>docstring' w' acc
          | doc  p c =>
            let n : string := (String (ascii_of_nat p) "") in 
            docstring' w' ("Port Ascii(" ++ n ++ ") "++c ++ "\n" ++ acc)
        end
    end.
  Definition docstring {c} (w:wiring c) := docstring' w "".
  Fixpoint output_pins {c} (l:wiring c) s: set pin :=
    let add_i := set_add%nat nat eq_nat_dec in
    match l with
      | [] => s
      | w::w' =>
    match w with 
      | watch_set n from fn to =>
        output_pins w' (add_i  to s)
      | just_set  fn to =>
        output_pins w' (add_i to s)
      | doc _ _ =>  output_pins w' s
    end
    end.

  Fixpoint input_pins {c} (l:wiring c) s: set pin :=
    let add_i := set_add%nat nat eq_nat_dec in
    match l with
      | [] => s
      | w::w' =>
        match w with 
          | watch_set n from fn to =>
            output_pins w'
                        (fold_left (fun se f => add_i f se) s  from)

          | just_set  fn to =>  output_pins w' s
          | doc  _ _ =>  input_pins w' s
        end
    end.

  Fixpoint all_pins {c} (l:wiring c) (s:set pin): set pin :=
    let add_i := set_add%nat nat eq_nat_dec in
    match l with
      | [] => s
      | w::w' =>
    match w with 
      | watch_set n  from fn to =>
        all_pins w'
                  (let new := (List.cons to (to_list from)) in
                  (List.fold_left (fun se f => add_i f se) s new))

      | just_set  fn to =>  all_pins w' (add_i to s)
      | doc  to _ =>  all_pins w' (add_i to s)
                               end
    end.
  Definition pins {c} (w:wiring c)  := of_list (all_pins w List.nil).
  (* Checks that all observers have a source and that only one setter per nat *)

  Definition writes c :=
    match c with
      | just_set _ _ => True
      | watch_set _ _ _ _ => True
      | _ => False
    end.

  Definition w_writes_to_p {n} (w:wiring n) p :=
    Exists (fun c =>
    match c with
      | just_set _ to 
      | watch_set _ _ _ to => to = p
      | _ => False
    end) w.
  Fixpoint pins_readable {c} (w:wiring c) : Prop :=
    Forall (fun f => match f with
                       | watch_set _ from _ to => Forall (w_writes_to_p w) from
                       | just_set _ to => w_writes_to_p w to
                       | _ => True
                     end) w.

  (* Inductive Unique {A} (P:A->Prop): forall {n}, t A n -> Prop := *)
  (* | Unique_hd_sat {m} x (v: t A m): P x -> Unique P (x::v) *)
  (* | Unique_hd_unsat {m} x (v: t A m): ~ P x -> Unique P (x::v)  *)
  (* | Unique_cons_sat {m} x (v: t A m): Unique P v -> ~ P x -> Unique P (x::v) *)
  (* | Unique_cons_unsat {m} x (v: t A m): Unique P v  ->  P x -> Unique P (x::v) . *)

  (* Inductive Unique {A} (P: A -> Prop): forall {n} (v: t A n), bool -> Prop := *)
  (*   | Unique_cons_unsat {n} x (v: t A n): ~ P x -> Unique P v false -> Unique P (x::v) false *)
  (*   | Unique_cons_sat {n} x (v: t A n): P x -> Unique P v false -> Unique P (x::v) true. *)
  Fixpoint Count {A n}  (P:A->bool)   (v: Vector.t A n) :=
    fold_left (fun s a => if P a then S (s) else s) 0 v.
  Hint Unfold Count.
  (* Theorem testunique : Count (beq_nat 0)  ((vseq 0 10)) = 1. *)
  (* Proof. *)
    
  (*   compute. *)
  (*    reflexivity. *)
  (* Qed. *)
  (* Theorem testunique2 : Count (beq_nat 1)  (1::(vseq 0 10)) = 1-> False. *)
  (* Proof. *)
    
  (*   compute. *)
  (*   intros. *)
  (*   inversion H. *)
  (* Qed. *)

  (* Definition Unique {A n} P (v: t A n):= Count P v = 1. *)
  (* Require Import Omega. *)

  (* Theorem Unique_dec : forall {A n} P (v:t A n), {Unique P v} + {~ Unique P v}. *)
  (*   intros. *)
  (*   induction v. *)
  (*   unfold Unique. *)
  (*   right. *)
  (*   simpl. *)
  (*   omega. *)

  (*   unfold Unique. *)
  (*   unfold Count. *)
    
  (*   unfold fold_left. *)
  (*   destruct P. *)
  (*   Qed. *)
  (* Theorem testunique2 :  ~ Unique (fun f => f = 0) (10::(vseq 0 11)) True . *)
  (* Proof. *)
  (*   unfold not. *)
  (*   intros. *)
  (*   simpl in H. *)
  (*   inversion H. *)
  (*   rewrite H3. *)
  (*   auto. *)
  (*   inversion H4. *)
  (*   unfold not in H4. *)



  (*   Qed. *)

  (* Theorem testunique : Unique (fun f => f = 0) ((vseq 0 10)) True . *)
  (* Proof. *)
   
  (*   compute. *)
  (*   intros. *)
  (*   repeat (constructor; auto). *)
  (*   Qed. *)
  Definition opt_output_pins {n} (w:wiring n) :=
    map (fun f => match f with
                       | watch_set _ _ _ to
                       | just_set _ to => Some to
                       | _ => None
                     end) w.
  Fixpoint pins_no_overlap {c} (w:wiring c) : Prop :=
    let p :=  (opt_output_pins w) in
    Forall (fun f => match f with
                       | watch_set _ _ _ to
                       | just_set _ to =>
                         1 = Count (fun f => match f with Some v => beq_nat to v | _ => false end) p
                       | _ => True
                     end) w.
  Definition valid_wiring {n} (w:wiring n) :=
    pins_readable w /\ pins_no_overlap w. 

  Require Import Omega.

Ltac solve_pins_readable :=
  repeat (constructor; auto; repeat (apply Exists_cons_tl;  
try (apply  Exists_cons_hd; reflexivity))).

Ltac solve_pins_no_overlap :=
  repeat (constructor; auto; repeat (apply Exists_cons_tl;  
try (apply  Exists_cons_hd; reflexivity))).
Ltac autowire := unfold valid_wiring; split; try (solve_pins_readable); try (solve_pins_no_overlap).

  (* Rewire w1 so it won't interfere with w2 *)
  Definition wire_add_offset n w1: component :=
    match w1 with
      | watch_set n from fn to =>
        (watch_set  (Vector.map  (fun x=>x+ n) from) fn (to+n))
      | just_set  fn to =>
        just_set fn (to+n) 
      | doc  p c =>  
        doc   (p+n) c
    end.
  Definition rewire {c c'} (w1: wiring c) {w2 : wiring c'} :wiring c  :=
    let m := Vector.fold_left max  0 (pins w2)in
    Vector.map (wire_add_offset (m+1)) w1.

  Theorem rewire_safe : forall {c c'} (w:wiring c) (w':wiring c'),
                          valid_wiring w ->
                          valid_wiring w' ->
                          valid_wiring ((@rewire c c' w w') ~&~ w').
    intros.
    induction w.
    auto.
    unfold rewire.
    assert (H1:forall (A B: Type) (a:A) c (b:Vector.t A c) (f: A-> B) f, Vector.map f (a::b) = (f a) :: (@Vector.map A B   f c b)).
    intros.
    auto.
    rewrite H1; auto.

    remember (wire_add_offset ((fold_left max 0 (pins w') )+1)) as f.
    unfold valid_wiring.
    remember (f h).
    case c;
    unfold append;
    intros;
    try split;
    auto; admit.

  Qed.
End Wires.