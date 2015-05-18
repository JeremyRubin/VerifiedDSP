Require Import String.
Require Import Ascii.
Require Import List.
Require Import ListSet.
Require Import EqNat.
Import ListNotations.
Require Import Arith.
Open Scope list_scope.

Require Import IOModule.

Module Wiring(IO:IO_SIG).
  Inductive wiring :=
  | base :  wiring
  | watch_set :  wiring -> list nat -> IO.func -> nat ->  wiring
  | just_set : wiring  -> IO.func -> nat -> wiring
  | join : wiring -> wiring -> wiring
  | doc : wiring -> nat -> string -> wiring.
  Notation  "w //  m ~> f ~>  n" := (watch_set w m f n) (at level 80, m at next level) : wiring_scope. 
  Notation  "w */  f ~>  n" := (just_set w f n) (at level 80, m at next level): wiring_scope. 
  Notation "w1 ~&~ w2" := (join w1 w2) (at level 80) : wiring_scope.
  Notation "w # p c " := (doc w p c) (at level 80, p at level 0) : wiring_scope.
  Open Scope wiring_scope.

  Open Scope string_scope.
  Fixpoint docstring' w acc :=
    match w with
      | base  => acc
      | watch_set w' from fn to => docstring' w' acc
      | just_set w' fn to =>docstring' w' acc
      | join w1 w2 => docstring' w2 (docstring' w1 acc)
      | doc w' p c =>
        let n : string := (String (ascii_of_nat p) "") in 
        docstring' w' ("Port Ascii(" ++ n ++ ") "++c ++ "\n" ++ acc)

    end.
  Definition docstring w := docstring' w "".
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
      | doc w' _ _ =>  output_pins w' s
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
      | doc w' _ _ =>  input_pins w' s
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
      | doc w' _ _ =>  all_pins' w' s
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
      | doc w' _ _ =>  valid_wiring' w'  ins outs
    end.
  Definition valid_wiring w : Prop :=
    valid_wiring' w nil nil.

  Require Import Omega.
  Ltac autowire :=
    unfold valid_wiring;
    unfold valid_wiring';
    simpl;
    repeat (try split; try omega).

  (* Rewire w1 so it won't interfere with w2 *)
  Fixpoint rewire_offset w1 n: wiring :=
    match w1 with
      | base => base
      | watch_set w' from fn to =>
        (watch_set  (rewire_offset w' n) (map (fun x=>x+ n)from) fn (to+n))
      | just_set w' fn to =>
        just_set  (rewire_offset w' n) fn (to+n) 
      | join w1 w2 =>
        join (rewire_offset w1 n) ( rewire_offset w2 n ) 
      | doc w' p c =>  
        (doc  (rewire_offset w' n ) (p+n) c)
    end.
  Definition rewire w1 w2 : wiring :=
    let m := fold_left max (pins w2) 0 in
    rewire_offset w1 (m+1).

  Theorem rewire_safe : forall w w',
                          valid_wiring w ->
                          valid_wiring w' ->
                          valid_wiring (rewire w w' ~&~ w').
    intros.
    unfold valid_wiring.
    unfold valid_wiring'.
    simpl.
    fold valid_wiring'.
    fold valid_wiring.
    split.
    admit.
    admit.
  Qed.
End Wiring.