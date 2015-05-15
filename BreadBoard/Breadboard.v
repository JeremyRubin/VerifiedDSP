
Require Import List.
Require Import ListSet.
Require Import EqNat.
Import ListNotations.

Require Import Arith.
Open Scope list_scope.
Module Type IO_SIG.
  Variable t : Type.
  Variable trace : Set.
  Variable func : Set.
  Variable nargs : func -> nat.
End IO_SIG.

Module IO.
  Definition t :=  nat.
  Definition trace := list (list t).
  Inductive func_ :=
  | fn_args : nat -> (trace -> t) -> func_.
  Definition func := func_.
  Definition nargs f :=
    match f with
      | fn_args n _ => n
    end.
End IO.

Module Type Component_Sig(IO:IO_SIG).
  Variable io : IO.func.
End Component_Sig.

Module Component(I:IO_SIG)(M:Component_Sig(I)).
  Import M.
  Definition io := M.io.
End Component.

Module Wiring(IO:IO_SIG).
  Inductive wiring :=
  | base :  wiring
  | watch_set :  wiring -> list nat -> IO.func -> nat ->  wiring
  | just_set : wiring  -> IO.func -> nat -> wiring
  | join : wiring -> wiring -> wiring.
  Notation  "w //  m ~> f ~>  n" := (watch_set w m f n) (at level 80, m at next level). 
  Notation  "w */  f ~>  n" := (just_set w f n) (at level 80, m at next level). 

  Notation "w1 ~&~ w2" := (join w1 w2) (at level 80).


  Fixpoint output_pins w s: set nat :=
    let add_i := set_add%nat nat eq_nat_dec in
    match w with 
      | base  =>
        s
      | watch_set w' from fn to =>
        output_pins w' (add_i  to s)
      | just_set w' fn to =>
        output_pins w' (add_i to s)
      | join w1 w2 => set_union%nat nat eq_nat_dec (output_pins w1 s) (output_pins w2 nil)
    end.

  Fixpoint input_pins w s: set nat :=
    let add_i := set_add%nat nat eq_nat_dec in
    match w with 
      | base  => s
      | watch_set w' from fn to =>
        output_pins w'
                    (fold_left (fun se f => add_i f se) s  from)

      | just_set w' fn to =>  output_pins w' s
      | join w1 w2 => set_union%nat nat eq_nat_dec (output_pins w1 s) (output_pins w2 nil)
    end.

  Fixpoint all_pins' w s: set nat :=
    let add_i := set_add%nat nat eq_nat_dec in
    match w with 
      | base  => s
      | watch_set w' from fn to =>
        all_pins' w'
                  (add_i to (fold_left (fun se f => add_i f se) s  from))

      | just_set w' fn to =>  all_pins' w' (add_i to s)
      | join w1 w2 => set_union%nat nat eq_nat_dec (all_pins' w1 s) (all_pins' w2 nil)
    end.
  Definition pins w := all_pins' w nil.
  (* Checks that all observers have a source and that only one setter per nat *)
  Fixpoint valid_wiring' w ins outs: Prop :=
    let add_i := set_add%nat nat eq_nat_dec in
    let notin := (fun el  s => (not (set_In%nat nat  el s))) in
    let union := set_union%nat nat eq_nat_dec in
    let intersect := set_inter%nat nat eq_nat_dec in
    match w with 
      | base  =>
        (* Check that the intersection of inputs and outputs is inputs,
         ie, everything can be read *)
        (intersect ins outs) = ins
      | watch_set w' from fn to =>
        notin to outs /\
        IO.nargs fn = length from /\
        valid_wiring' w'
                      ( fold_left  (fun s f => add_i f s) ins from) (add_i to outs)
      | just_set w' fn to=>
        notin to outs
        /\ valid_wiring' w' ins (add_i to outs)
      | join w1 w2 =>
        let w1_out := output_pins w1 [] in
        let w2_out := output_pins w2 [] in
        (* intersect w1_out w2_out = [] /\ (*is implicitly checked*)  *) 
        (* We union in the others outputs to say that w2 is promising
        that it will make this available as an output (so treat it as an
        available input too *)
        valid_wiring' w1 (union w2_out ins) (union
                                               w2_out outs) /\
        valid_wiring' w2  (union w1_out ins) (union w1_out outs)
    end.
  Definition valid_wiring w : Prop :=
    valid_wiring' w nil nil.

  Require Import Omega.
  Ltac autowire :=
    unfold valid_wiring;
    unfold valid_wiring';
    simpl;
    repeat (try split; try omega).
End Wiring.


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

  Fixpoint find_trace p pt : list IO.t :=
    match pt with 
      | nil => nil
      | (p', t)::rest => if beq_nat p' p then t else find_trace p rest
    end.
  Definition find_traces (p :list nat) (pt : list (nat * list IO.t)) : list (list IO.t) :=
    map (fun f =>  (find_trace f pt))  p.

  Definition any_trace  (pt : list (nat * list IO.t) ): list IO.t :=
    match pt with 
      | nil => nil
      | (p', t)::rest => t
    end.
  Fixpoint update_trace pt u acc:=
    match u with
      | (p, iot)::rest =>
        update_trace pt rest ((p, iot::(find_trace p pt))::acc)
      | nil => acc
    end.
  Print IO.func.
  Fixpoint step' w pt (u : list (nat * IO.t))  :=
    let add_i := set_add in 
    match w with 
      | base  =>
        update_trace pt (u) nil
      | watch_set w' from (IO.fn_args n fn) to =>
        let traces := (find_traces from pt) in
        step' w' pt ((to, fn traces )::u)
      |  just_set w' (IO.fn_args n fn) to =>
         step' w' pt  ((to, fn [any_trace  pt ])::u)
      | join w1 w2 =>
        step' w2 pt [] ++ step' w1 pt u
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


Definition demo1 := base
                      */  zero_rail ~> 0
                      //  [5] ~> integrator~> 6
                      // [2] ~> integrator~> 3
                      */ incrementor ~> 2
                      */ IO.fn_args 0 (fun _=> 10) ~> 5
                      */ alternator ~> 8.

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

Theorem alternates: forall n,
                      let tr := run demo1 n in
                      let a :=find_trace 8 tr in
                      n >2 -> (hd 0 a) <> (hd 0 (tl a)).
Proof.
  intros.

  intros.
  induction n.
  inversion H.

  unfold run, run', step', update_trace, demo1 , alternator, integrator, zero_rail,
  incrementor, find_trace , update_trace, pin_trace_gen, pins, output_pins, length, alt,
  set_add, set_remove, set_inter in tr.
  simpl in tr.

  unfold a.
  admit. (** :( **)
Qed.