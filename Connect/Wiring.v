
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

Require Import Vector.
Import Vector.
Module Wiring.
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
  Fixpoint valid_wiring' {c} (w:wiring c) ins outs: Prop :=
    let add_i := set_add%nat nat eq_nat_dec in
    let notin := (fun el  s => (not (set_In%nat nat  el s))) in
    let union := set_union%nat nat eq_nat_dec in
    let intersect := set_inter%nat nat eq_nat_dec in
    match w with
      | [] =>
        (* Check that the intersection of inputs and outputs is inputs,
         ie, everything can be read *)
        (intersect ins outs) = ins
      | w::w' =>
    match w with 
      | watch_set n from fn to =>
        notin to outs /\
        (* IO.nargs fn = length from /\ *)
        valid_wiring' w'
                      ( fold_left  (fun s f => add_i f s) ins from) (add_i to outs)
      | just_set  fn to=>
        notin to outs
        /\ valid_wiring' w' ins (add_i to outs)
      | doc  _ _ =>  valid_wiring' w'  ins outs
                                   end
    end.
  Definition valid_wiring {c} (w: wiring c) : Prop :=
    valid_wiring' w List.nil List.nil.

  Require Import Omega.
  Ltac autowire :=
    unfold valid_wiring;
    unfold valid_wiring';
    simpl;
    repeat (try split; try omega).

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
    unfold valid_wiring'.
    remember (f h).
    case c;
    unfold append;
    intros;
    try split;
    auto; admit.

  Qed.
End Wiring.