
Require Import List.
Require Import ListSet.
Require Import EqNat.

Require Import Arith.
   Open Scope list_scope.
Module Type IO_SIG.
  Variable t : Type.
  Variable func : Set.
End IO_SIG.

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
  | watch_set :  wiring -> nat -> IO.func -> nat ->  wiring
  | just_set : wiring  -> IO.func -> nat -> wiring.
Notation  "w //  m ~> f ~>  n" := (watch_set w m f n) (at level 80, m at next level). 
Notation  "w */  f ~>  n" := (just_set w f n) (at level 80, m at next level). 


(* Checks that all observers have a source and that only one setter per nat *)
Fixpoint valid_wiring' w ins outs: Prop :=
  let add_i := set_add%nat nat eq_nat_dec in
  let notin := (fun el  s => (not (set_In%nat nat  el s))) in
  match w with 
    | base  =>
      (set_inter%nat nat eq_nat_dec ins outs) = ins
    | watch_set w' from fn to =>
      notin to outs /\  valid_wiring' w' ( add_i from ins) (add_i to outs)
    | just_set w' fn to=>
      notin to outs /\ valid_wiring' w' ins (add_i to outs)
  end.
Definition valid_wiring w : Prop :=
  valid_wiring' w nil nil.

Require Import Omega.
Ltac autowire :=
    unfold valid_wiring;
    unfold valid_wiring';
    unfold not;unfold set_add, set_In, set_inter, In;simpl;
    repeat (try split; try omega).

End Wiring.

Module IO.
  Definition t := nat.
  Definition func := list t -> t.
End IO.

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

  Fixpoint pins' w s: set nat :=
    let add_i := set_add%nat nat eq_nat_dec in
    match w with 
      | base  => s
      | watch_set w' from fn to => pins' w' (add_i from (add_i to s))
      | just_set w' fn to =>  pins' w' (add_i to s)
    end.
  Definition pins w := pins' w nil.

  Definition pin_trace_gen w : list (nat* list IO.t):= map (fun p => (p, nil)) (pins w).

  Fixpoint find_trace p pt : list IO.t :=
    match pt with 
      | nil => nil
      | (p', t)::rest => if beq_nat p' p then t else find_trace p rest
    end.

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
  Fixpoint step' w pt (u : list (nat * IO.t))  :=
    let add_i := set_add in 
    match w with 
      | base  =>
        update_trace pt (u) nil
      | watch_set w' from fn to =>
        step' w' pt ((to, fn (find_trace from pt ))::u)
      |  just_set w' fn to =>
         step' w' pt  ((to, fn (any_trace  pt ))::u)
    end.
  Definition step w :=
    step' w (pin_trace_gen w) nil.

  Fixpoint run' (w:wiring) (pt: list (nat * list IO.t)) fuel  :=
    match fuel with
      | O => pt
      | S n => run' w (step' w pt nil) n
    end.
  Definition run w fuel :=
    run' w (pin_trace_gen w) fuel.
End IORUN.






Import IORUN.

Module Integrator_Spec.
  Definition io (x:list IO.t):IO.t := suml x.
End Integrator_Spec.
Module Incrementor_Spec.
  Definition io (x:list IO.t):IO.t := len x.
End Incrementor_Spec.


  Fixpoint alt x start:=
    match x with
      | O => start
      | S n => alt n (if beq_nat start 0 then 1 else 0)
    end.
Module Alternator_Spec.
  Require Import Arith.Even.
  Definition io (x:list IO.t):IO.t := alt (length x) 1.
End Alternator_Spec.

Module Integrator := Component(IO)(Integrator_Spec).
Module Incrementor := Component(IO)(Incrementor_Spec).
Module Alternator := Component(IO)(Alternator_Spec).


Definition integrator(x:list IO.t):IO.t := suml x.
Definition incrementor (x:list IO.t):IO.t := len x.
Definition alternator (x:list IO.t):IO.t := alt (length x) 1.
Definition zero_rail (x:list IO.t):IO.t := 0.


Definition demo1 := base
                       */  zero_rail ~> 0
                      //  5 ~> integrator~> 6
                      // 2 ~> integrator~> 3
                      */ incrementor~> 2
                      */ (fun _=> 10) ~> 5
                      */ alternator ~> 8.

Theorem good_build : valid_wiring demo1.
Proof. 
  autowire.
Qed.
Compute (find_trace 3 (run demo1 10)).

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
incrementor, find_trace , update_trace, pin_trace_gen, pins, pins', length, alt,
set_add, set_remove, set_inter in tr.
simpl in tr.

unfold a.
admit. (** :( **)
Qed.