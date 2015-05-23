
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
Require Import EqNat.
Require Import Arith.

Require Import Vector.
Import Vector.
Import VectorNotations.


Require Import IOModule.
Require Import Common.
Require Import Wiring.
Import Wires.


Module IORUN.

  Definition opt_trace c := option (IO.trace c).

  Definition find_trace {c n :nat}   (pt: pintrace n c )  (p:pin): opt_trace c :=
    match lt_dec p n with
      | left pf => nth pt (Fin.of_nat_lt  pf)
      | right r=> None
    end.
  
  
  Definition find_traces {c n pn:nat}
             (pt :pintrace n c) (p :Vector.t pin  pn): pintrace pn c:=
    Vector.map (find_trace pt)  p.


  Definition any_trace {c n:nat}  (pt : pintrace n c ): IO.trace c:=
    Vector.const 0 c.

  Definition find_update {n:nat}  (p:pin) (u: pinupdate n)  : option (IO.t) :=
    match lt_dec p n with
      | left pf => nth u (Fin.of_nat_lt  pf)
      | right r=> None
    end.


  Definition defhd {A n} (d: A) (v:Vector.t A n):=
    match v with
      | v'::_ => v'
      | [] => d
    end.

  
  Require Import NPeano.
  Require Import Arith.
  Definition elim_0 {T c} (m: Vector.t T (c+0)) : Vector.t T (c).
    rewrite plus_comm in m.
    simpl in m.
    apply m.
    Defined.
    
  Definition elim_opt {T} (o:option T) (pf: o <> None) : T.
    destruct o.
    exact t.
    unfold not in pf.
    contradiction pf.
    reflexivity.
    Defined.
  Definition conv_proof {T n} (m: Vector.t (option T) n)  (pf: Forall (fun f =>  f <> None) m) (o : option T) (pf2 : In o m) : T.
    destruct o.
    exact t.
    admit. (* Should be easy? *)

    Qed.
  (*CR Nickolai: How can I Eliminate the default parameter given that it is
   never used *)
    Theorem in_dec {n T} (T_eq_dec: forall (a b:T), {a = b} + {a<>b}) (m: Vector.t T n) (v:T) : {In v m} + {~ In v m}.


     induction m.

     right.
     unfold not ;intros; inversion H.
     
     elim IHm.
     left.
     constructor.
     apply a.
     
      assert ({v = h} + {v <> h}).
      apply T_eq_dec.
      elim H.
      intros.
      left.
      rewrite a.
      constructor.
      intros.
      right.
      unfold not.
      intros.
      apply b.
      admit. (** This one seems easy to prove but IDK *)
      
      Qed.

  Definition sequenceOpt {T c} (m: Vector.t (option T) c) default :=
    match  seq_dec m with
      | left pf =>
        Some (map (fun f=>
                     match f with
                       | None => default
                       | Some t => t
                     end )
                     m) 
      | right pf => None
    end.
  
  Compute (sequenceOpt [Some 1; None] 3).
  Definition update_trace {c n : nat}
             (pt:pintrace n c)
             (u: pinupdate n) :
    pintrace n (S c) :=
    map2 (fun (pv:opt_trace c) up =>
            match pv , up with
              | Some t, Some update=> Some ( update ::t)
              | Some t, None => Some ((defhd 0 t)::t)
              | None, _ => None 
            end
         )pt u.

  Definition next_value {c n} (pt: pintrace n c)  w  :=
    let imaginary_default := (Vector.const 0 c) in
    match w with 
      | watch_set n from fn to =>
        let mt := sequenceOpt (find_traces pt from)  imaginary_default in
        match mt with
          | None => None
          | Some traces => Some (fn  c traces)
        end
      |  just_set fn to => Some (fn c [any_trace pt])
      | doc _ _ => None
    end.
  
  Section Canon.
    Fixpoint findf {n} w p : option (component) :=
      match w with
        | a :: r =>
          match a with
            | just_set _ to as c
            | watch_set _ _ _ to as c=>
              if eq_nat_dec to p then
                Some c
              else
                findf r p
            | doc _ _ => findf r p
          end
        | [] => None
      end.
    Definition canonical_wiring := fun n => Vector.t (option component ) n.

    
    Definition canonicalize_wiring {n} (w:wiring  n) :=
      let d := S (Vector.fold_left max 0 (pins w)) in 
      match  n as n' return (match n' with
                               | O=> canonical_wiring 0
                               | _ => canonical_wiring d
                             end)
      with
        | S n => map (findf w) (vseq 0 d)
        | 0 => [] 
      end.
  End Canon.
  Definition step {c n} {fns: canonical_wiring n} (pt :pintrace n c) :=
    let res := Vector.map (fun f => match f with Some c => next_value pt c | None => None end)  fns in
    update_trace pt res.


  Definition pin_trace_gen   {n} {fns: canonical_wiring n} :
    Vector.t (opt_trace 0) n :=
      Vector.map (fun p => match p with | None => None | _ =>Some [] end ) fns.


  Fixpoint run' {n} (fns: canonical_wiring n) fuel :=
    match fuel with
      | S f => @step _ n fns (run' fns f)
      | O =>  @pin_trace_gen n fns
    end.
  
  (*CR Nickolai : Can I make this function work (and not be annoying!) with the commented out bits? *)
  Definition run {n} (w:wiring (S n)) fuel :=
    (* match w as w return (match w with *)
    (*                        | [] => pintrace 0 fuel *)
    (*                        |  (v::v') as w' => pintrace _ fuel *)
    (*                      end) *)
    (* with *)
    (*   | [] => [] *)
    (*   | (v::v') as w' => *)
        let fns := canonicalize_wiring w in
        run' fns fuel.
    (* end. *)

End IORUN.


Import IORUN.