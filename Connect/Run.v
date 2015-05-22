
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

  
  (*CR Nickolai: How can I Eliminate the default parameter given that it is
   never used *)
  Definition sequenceOpt {T c} (m: Vector.t (option T) c) default :=
    match  seq_dec m with
      | left pf =>
        Some (map (fun f =>
                     match f  with
                       | None => default
                       | Some t => t
                     end) m) 
      | right pf => None
    end.
  
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
  
  Fixpoint vseq (from to:nat) :=
    match to with
      | O => []
      | S n => ( from) ::vseq (S from) n
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