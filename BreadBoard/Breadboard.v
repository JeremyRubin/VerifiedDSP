 Require Import String.
 Require Import Ascii.
Require Import List.
Require Import ListSet.
Require Import EqNat.
Import ListNotations.
Require Import Arith.
Open Scope list_scope.

Notation "$ x" := (fun f => f x) (at level 0, right associativity, only parsing).
Notation "f $ x .. y" := (.. (f x) .. y) (at level 0, right associativity, only parsing).






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

Module Wires := Wiring(IO).
Import Wires.

Module IORUN.


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






Import IORUN.

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

Definition p := 1.
Definition s := "Hello".
Definition demo1 := base
                      */  zero_rail ~> 0
                      //  [5] ~> integrator~> 6
                      // [2] ~> integrator~> 3
                      */ incrementor ~> 2
                      */ IO.fn_args 0 (fun _=> 10) ~> 5
                      */ alternator ~> 8
                      # 2 "com".
Compute (docstring demo1).
Definition demo2 := base */integrator ~> 9
                         // [6] ~> delay_n 5 0 ~> 10.

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

