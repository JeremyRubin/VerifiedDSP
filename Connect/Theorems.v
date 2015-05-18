
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
Require Import c8051.
Import i8051_Component.
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
Theorem non_interference1 : forall w w', valid_wiring w ->
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
Theorem non_interference2 : forall w w', valid_wiring w ->
                                        valid_wiring w' ->
                                        valid_wiring  (w ~&~ w') ->
                                        forall n t,
                                         find_trace t (run w n)=
                                         find_trace t (run (w ~&~ w') n).
admit.
Qed.

(* Funcs are the same*)
Print IO.trace.
Definition func_same (i i':IO.func) := forall (tr:IO.trace),
                                                let lengths := (map (fun x => length x) tr) in 
                                                let fl := hd 0 lengths in
                                                fold_left (fun acc  x =>x=fl/\acc)  lengths True->
                                             match i, i' with
                                               |IO.fn_args n f, IO.fn_args n' f'=>
                                                length tr = n ->
                                                f tr = f' tr /\ n = n'
                                             end.
Compute (length [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1]).

Theorem simulates :  func_same (i8051_Component [2;0;0] threshold dac) (IO.fn_args (8*4) (fun _ => 0)).
Proof.

  unfold dac.
  unfold func_same.
  intros.
  unfold i8051_Component.
  intros.

  destruct tr as [| a l] .
  inversion H0.



repeat ( let x:= fresh in destruct l as [| x  l]; inversion H0).

unfold length in *.
split;auto.





unfold map, fold_left, hd in H.


decompose [and] H.

unfold traces.

simpl.
unfold to_trace, condense', condense.


unfold run_8051_bin_string, run_8051, i8051Semantics.dump_state, i8051Semantics.load_code_bytes_bin, i8051Semantics.nsteps_init.
simpl.




unfold i8051Semantics.nsteps, i8051Semantics.step.
unfold  i8051Semantics.run_rep .



unfold i8051Semantics.i8051_RTL.flush_env.
unfold i8051Semantics.i8051_RTL.get_loc,
i8051Semantics.fetch_instruction,
i8051Semantics.RTL_step_list,
i8051Semantics.i8051_Decode.instr_to_rtl.



unfold i8051Semantics.i8051_Decode.runConv,
i8051Semantics.i8051_Decode.conv_ANL,
i8051Semantics.i8051_Decode.EMIT,
i8051Semantics.i8051_Decode.conv_SETB,
i8051Semantics.i8051_Decode.conv_CLR,
i8051Semantics.i8051_Decode.conv_LJMP,
i8051Semantics.i8051_Decode.conv_JMP,
i8051Semantics.i8051_Decode.conv_NOP.


unfold i8051Semantics.i8051_RTL.CodeMap.set.
unfold i8051Semantics.i8051_RTL.CodeIndexed.index.
unfold Maps.PMap.set.
unfold Maps.PTree.set.

unfold Maps.ZIndexed.index, i8051Semantics.i8051_RTL.CodeMap.init, Maps.PMap.init, fst, snd.
unfold dac.
unfold map.
unfold i8051Semantics.parse_instr.
unfold i8051Semantics.parse_instr_aux.

  admit.

  Qed.
Definition wrapper := IO.func -> IO.func.