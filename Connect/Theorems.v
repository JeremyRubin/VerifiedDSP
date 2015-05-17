
Add LoadPath "../Model".
Require Import String.
Require Import Ascii.
Require Import List.
Require Import ListSet.
Require Import EqNat.
Import ListNotations.
Require Import Arith.
Open Scope list_scope.
Open Scope string_scope.
Require Import Run.
Import Wires.
Require Import Breadboard.
Import BB.
Import IORUN.
Require Import IOModule.
Import IO.
Theorem good_build : valid_wiring (demo1 ~&~ demo2).
Proof. 
  autowire.
Qed.

Theorem bad_build : valid_wiring (demo1 ~&~ demo1) -> False.
Proof. 
  autowire.
Qed.

Compute (find_trace 10 (run (demo1 ~&~ demo2) 10)).

Theorem no_modify_history_update: forall pin_tr upd n,
                                    let a := (find_trace n (update_trace pin_tr upd [])) in
                                    let b := find_trace n pin_tr in
                                    match (a, b) with
                                      | (Some (a'::rest), Some rest') =>
                                        rest = rest'
                                      | _ => True
                                    end.
  intros.
  unfold a, b. 
  auto.
  generalize dependent pin_tr.
  induction upd.
  intros.
  induction pin_tr.
  simpl.
  auto.
  simpl.
  auto.
  intros.
  remember (find_trace n (update_trace pin_tr (a::upd) [] )).
  destruct o; auto.
  destruct  l; auto.
  remember (find_trace n pin_tr).
  destruct o; auto.
  admit.
Qed.
Theorem step_history_safe: forall l w n, 
                             l = tl (step' w l n).
  admit.
Qed.

Theorem no_modify_history: forall n w,  run  w n = tl (run w (S n)).
Proof.
  intros.
  induction n.
  unfold run, run'. 
  remember (pin_trace_gen w).
  apply step_history_safe.
  unfold run.
  remember (pin_trace_gen w).
  unfold run'.
  admit.
  (*  unfold run, run'. *)

  (* apply step_history_safe. *)
  
  (*  simpl. *)
  (*  apply no_modify_history_update. *)
Qed.

Check no_modify_history.
Theorem alternates:  forall n, let tr := run demo1 n in
                               let a :=find_trace 8 tr in
                               match a with
                                 | Some ( 0::1::rest)
                                 | Some (1::0::rest)  => True
                                 | Some [1] | Some [0] | Some [] => True
                                 | _ => False
                                          
                               end.
Proof.
  intros. destruct n.
  simpl.
  auto.
  unfold a.
  unfold tr.
  unfold run.
  remember (pin_trace_gen demo1).
  auto.
  destruct l;auto.
  simpl.
  auto.
  admit.
  admit.
Qed.

(* joined well formed circuits aren't interfered with by an additional module *)
Theorem non_interference : forall w w', valid_wiring w ->
                                        valid_wiring  (w ~&~ w') ->
                                        forall n t,
                                          let orig := find_trace t (run w n) in
                                          let mod := find_trace t (run (w ~&~ w') n) in
                                          match  orig, mod with
                                            | Some a, Some b => a = b
                                            | Some a, None => False
                                            | None, Some a => True
                                            | None, None => True
                                          end.
admit.
Qed.

(* Funcs are the same*)
Definition func_same  := forall tr (i i':IO.func),
                           match i, i' with
                             |IO.fn_args n f, IO.fn_args n' f'=>
                              f tr = f' tr /\ n = n'
                           end.


Definition wrapper := IO.func -> IO.func.