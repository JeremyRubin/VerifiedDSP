
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
Add LoadPath "../Model".
Require Import String.
Require Import Ascii.
Require Import EqNat.
Require Import Arith.
Open Scope string_scope.
Require Import Run.
Require Import Wiring.
Import Wires.
Require Import Breadboard.
Import IORUN.
Require Import IOModule.
Require Import c8051.
Import i8051_Component.
Import IO.

Require Import Vector.
Import VectorNotations.
Import Vector.
Open Local Scope vector_scope.
Check update_trace.
(* Demonstrate proving a build correct *)

Theorem good_build : valid_wiring (demo1 ~&~ demo2).
Proof.
  autowire.
Qed.
  

(* (* Demonstrate proving a build incorrect, double buld always bad if wiring writes anything *) *)
(* Theorem bad_build : valid_wiring (demo1 ~&~ demo1) -> False. *)
(* Proof.  *)
(*   autowire. *)
(* Qed. *)

(* Theorem join_self_if_writes__always_bad : forall {s} (w: wiring (S s)), Exists writes w -> ~ (valid_wiring (w ~&~ w)). *)
(* Proof. *)
(*   intros. *)
(*   unfold valid_wiring. *)
(*   unfold valid_wiring'. *)
  
(* CR Nickolai: cannot type check because (~ exists n, 0 = S n) for run function *)
(* Definition nil_wire : wiring 0 := []. *)
(* Lemma nil_run: *)
(*   forall x, *)
(*     Forall (fun f => f = None) (run nil_wire x) . *)
(* Proof. *)
  
(*   intros. *)
(*   apply Forall_nil. *)
(* Qed. *)

(* Theorem no_modify_history: *)
(*   forall c n (w:wiring (S c)) ,  valid_wiring w ->  *)
(*    Forall2 (fun f1 f2 => f1 = f2) (run   w n)  (map (option_map tl) (run w (S n))). *)
(* Proof. *)
(*   intros. *)

(*   induction n. *)

(*   unfold run at 1. *)

(*   unfold run, run', pin_trace_gen. *)
(*   unfold step. *)

(* Qed. *)

(* Compute  (run demo1 1). *)

Lemma alt_n_SSn : forall n, 
                    alt  n  = alt  (S (S n)) .
Proof.
  intros.
  auto.
Qed.
Lemma alt_n_Sn : forall n,

                   alt n <> alt (S n).
  Proof.

  intros.
  induction n.
  unfold alt.
  
  unfold alt_.
  auto.

  unfold alt.
  
  auto.
Qed.

  Lemma alt_in_01 : forall n, alt n < 2.

    intros.
    unfold alt.
    destruct alt_; auto.
    Qed.

  Lemma list_len_cons : forall {A} (l:list A) (b:A), S (length l )= length (List.cons b l).
  Proof.
intros.
auto.
    Qed.
  Lemma l1 : forall  n, alt n = alt (S (S n)) -> alt n <2 -> (alt n <> alt (S n)) ->  alt (S n) = 0 -> alt n =1.
    intros.
    
    unfold not in *.
    omega.
    Qed.
  Lemma l2 : forall n, alt (S n) = 0 -> alt n = 1.
    intros.
    apply l1.
    apply alt_n_SSn.
    apply alt_in_01.
    apply alt_n_Sn.
    apply H.
    Qed.

  Lemma l3 : forall  n, alt n = alt (S (S n)) -> alt n <2 ->
                        (alt n <> alt (S n)) ->  alt (S n) = 1 -> alt n =0.
    intros.
    
    unfold not in *.
    omega.
    Qed.
  Lemma l4 : forall n, alt (S n) = 1 -> alt n = 0.
    intros.
    apply l3.
    apply alt_n_SSn.
    apply alt_in_01.
    apply alt_n_Sn.
    apply H.
    Qed.
  Print alternator.

  Check alternator.
Lemma alternates' :
  forall {c} (l:Vector.t IO.t c) b,
            @alternator (S c)  ([b::l]) = 1 ->
    @alternator c [l] = 0.
Proof.
  intros. 
  auto.

  unfold alternator, hd in *.
  unfold Common.len in *.
  apply l4.
  
  apply H.
  
  Qed.

Lemma alternates'' :
  forall {c} (l:Vector.t IO.t c) b,
    @alternator c [l] = 0 ->
            @alternator (S c)  ([b::l]) = 1.
Proof.
  intros. 

  unfold alternator, hd in *.
  unfold Common.len in *.
  apply l2.
  
  rewrite <- alt_n_SSn.
  apply H.
  Qed.

Lemma alternator_alternates :
  forall {c} (l:Vector.t IO.t c) b,
    @alternator c [l] = 0 <->
            @alternator (S c)  ([b::l]) = 1.
Proof.
  intros.
  split.
  apply alternates''.
  apply alternates'.
  Qed.

Check find_trace.

Definition altCircuit {l} (w:wiring l) := canonicalize_wiring (w */ alternator ~> 1).



Check update_trace.
Print pintrace.
Definition pop_update {n c} (pt:pintrace n (S c)) : pintrace n c  :=
  map (fun f:(option (IO.trace (S c))) =>   option_map tl f) pt.

Lemma map_cons: forall (A B: Type) (a:A) c (b:Vector.t A c) (f: A-> B) f, Vector.map f (a::b) = (f a) :: (@Vector.map A B   f c b).
    intros.
    auto.
Qed.
Theorem map2nil0 : forall  {A B C} (a:t A 0) (f:C->A->B), map2 f [] a = [].
Proof.
  intros.
  remember (map2 f [] a).
  admit.
  Qed.

Theorem map2nil1 : forall  {A B C} (a:t C 0) (f:C->A->B), map2 f a [] = [].
Proof.

  admit.
Qed.

Theorem map2nil2 : forall  {A B C} (a:t C 0) (b: t A 0) (f:C->A->B), map2 f a b = [].
Proof.

  admit.
Qed.
Theorem safe_update : forall {n c} (pt: pintrace n c) (u:pinupdate n), pop_update (update_trace pt u) = pt.
  (* intros. *)
  (* unfold pintrace, pinupdate, trace in *. *)
  (* generalize dependent n. *)
  (* + intros. *)
  (*   induction c. *)
  (* - unfold update_trace. *)
  (*   induction n. *)
  (*   * apply case0. *)
  (*     rewrite map2nil2. *)
      
  (*     auto. *)
  (*   * *)
  (*     destruct pt. *)
  (*      rewrite map2nil2. *)
  (*     auto. *)
  (*     unfold pop_update. *)
     
  (*    apply IHn. *)
  (*    unfold update_trace. *)

  (* +intros. *)
  intros .
  admit.
Qed.
Check @step.
Theorem present' : forall  n,
                     let cw := altCircuit [] in
                     find_trace  (run' (cw) n) 1 <> None ->
                               find_trace (@step _ _   (cw) (run' (cw) n)) 1<> None.
Proof.
  intros.
  
  unfold cw,altCircuit,canonicalize_wiring in *;
  unfold find_trace in *.
  simpl in *.
  unfold step.
  simpl.
  unfold any_trace.
  remember (alternator n [const 0 n]).


  unfold run'.

  induction n.
  compute.
  intro H1; inversion H1.
  compute.
  unfold update_trace.

  Qed.
Theorem present : forall  n, find_trace 1 (run (altCircuit []) n) <> None.
  induction n.
  compute.
  intro H. inversion H.
  unfold run.
  fold @run.
  apply present'.
  auto.
  Qed.
Theorem alternates:  forall n, option_map hd (find_trace 1 (run altCircuit (S n))) =
                               option_map hd (option_map tl (find_trace 1 (run altCircuit (S(S n))))).
  Proof.
  intros.
  compute.
  unfold altCircuit.
  unfold run.
  unfold step.
  unfold option_map.
  simpl.
  unfold 
  compute.
                               match tr, tr' with
                                 | Some [], Some [1] 
                                 | Some ( 0::_), Some (1::_)
                                 | Some (1::_), Some (0::_)  => True
                                 | _,_ => False
                                          
                               end.
Proof.
  intros.
  destruct tr.
  destruct tr'.
  
  vm_compute.
  auto.

  unfold a.
  unfold tr.
  unfold run.
  unfold run'.
  fold run'. 

  fold run'.
  vm_compute.
  unfold demo1 in *.
  unfold integrator, incrementor, alternator, zero_rail in *.
  unfold Common.suml, Common.len in *.
  destruct pin_trace_gen;auto.
  simpl.
  auto.
  unfold run'.
  unfold find_trace.
  unfold step.
  unfold update_trace.
  unfold remove_none.
  unfold next_value.
  unfold map.
  simpl.

  unfold Vector.hd.
  unfold length.
  
  unfold alt.
  auto.
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
(* Compute (length [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1]). *)

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


unfold run_8051_bin_string, run_8051, i8051Semantics.dump_state, i8051Semantics.load_code_bytes_bin, i8051Semantics.nsteps_init.
unfold traces.
unfold map. simpl.
simpl.
unfold to_trace, condense', condense.

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
unfold i8051Semantics.parse_instr.
unfold i8051Semantics.parse_instr_aux.
destruct r.

admit.
  Qed.
Definition wrapper := IO.func -> IO.func.