
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
Open Scope list_scope.
Require Import IOModule.

Require Import Vector.
Import Vector.
Import VectorNotations.


Require Import Wiring.

Module Wires := Wiring.Wiring.

Module IORUN.
  Import Wires.


  Fixpoint find_trace {c n:nat}  (p:pin) pt  : option (IO.trace c) :=
    match p, pt with
        | O, a::b => a
        | S n, a::b => find_trace n b
        | _, _ => None
    end.
    (* @nth _ n pt p. *)
  Definition find_traces {c n pn:nat} (p :Vector.t _ pn) (pt :pintrace n c)
  : Vector.t (option (IO.trace c)) pn:=
    Vector.map (fun f =>  (find_trace f pt))  p.
    (* let none_missing := forallb (fun x => match x with | None => false | _ => true end ) (Vector.to_list elts) in *)
    (* if none_missing then  *)
    (*   Some (Vector.map *)
    (*           (fun f : option (Vector.t IO.t c) => *)
    (*              match f with *)
    (*                | None => Vector.const 0 c *)
    (*                | Some x => x *)
    (*              end) elts) *)
    (* else None. *)

  Fixpoint any_trace {c n:nat}  (pt : pintrace n c ): IO.trace c:=
    match pt with 
      | [] => Vector.const 0 c
      | None::rest => any_trace rest
      | Some  t::rest => t
    end.
  (* Fixpoint update_trace' {c n d:nat} (pt:Vector.t (nat * Vector.t IO.t c) n) *)
  (*          (u:Vector.t (nat * IO.t) d)  *)
  (*          (acc : list (nat * Vector.t IO.t (S c))  ): *)
  (*           list (nat * Vector.t IO.t (S c))  := *)
  (*   match u with *)
  (*     | (p, iot)::rest => *)
  (*       match find_trace p pt with *)
  (*         | None => update_trace' pt rest  acc *)
  (*         | Some tr => *)
  (*        update_trace' pt rest ((p, iot::tr)::acc) *)
  (*       end *)
  (*     | [] =>  acc *)
  (*   end. *)
  (* Definition update_trace'' {c n d: nat} (pt:Vector.t (nat * Vector.t IO.t c) n) *)
  (*            (u: (nat * IO.t))  *)
  (*          (acc : Vector.t  (nat * Vector.t IO.t (S c)) d ): *)
  (*          Vector.t  (nat * Vector.t IO.t (S c)) (S d) := *)
  (*     let (p,v) :=  u in  *)
  (*       match find_trace p pt with *)
  (*         | None => (p, Vector.const 0 (S c))::acc *)
  (*         | Some tr => *)
  (*        ((p, v::tr)::acc) *)
  (*       end. *)
  Fixpoint find_update {n:nat}  p (u: pinupdate n)  : option (IO.t) :=
    match p, u with
        | O, a::b => a
        | S n, a::b => find_update n b
        | _, _ => None
    end.
    (* @nth _ n u p. *)
    (* match u with  *)
    (*   | [] => None *)
    (*   | Some v::rest => if beq_nat p' p then Some t else find_update  p rest  *)
    (* end. *)
  Definition defhd {A n} (d: A) (v:Vector.t A n):=
    match v with
      | v'::_ => v'
      | [] => d
    end.
    Check (andb).
    Check @fold_left.
  Definition sequenceOpt {T c} (m: Vector.t (option T) c) def :=
    let allg := fold_left (fun p v => andb p match v with Some _ => true | None => false end) true m in
    if  allg then
      Some (map (fun f =>
                   match f  with
                     | Some t => t
                     | None => def
                end) m) 
      else None.
      
    (* fix seqOpt {n m} (mv: Vector.t (option T) (S m)) : Vector.t T (n) := *)
    (* match mv with *)
    (*   | None ::_ => None *)
    (*   | Some x::r::s => @seqOpt _ _ (x::acc) (r::s) *)
    (*   | [Some x] => Some (acc) *)
    (*   | [] => Some acc *)
    (* end. *)
  Definition update_trace {c n : nat}
             (pt:pintrace n c)
             (u: pinupdate n) :
    pintrace n (S c) :=
    map2 (fun (pv:(option (IO.trace c))) up =>
           match pv , up with
               | Some t, Some update=> Some ( update ::t)
               | Some t, None => Some ((defhd 0 t)::t)
               | None, _ => None 
           end
             )pt u.

  Require Import Vector.
  Check (Fin.of_nat 10 1).
  Check find_traces.
  Check (IO.trace).
  Fixpoint next_value {c n} (pt: pintrace n c)  w  :=
    
    match w with 
      | watch_set n from fn to =>
        match sequenceOpt (find_traces from pt) (Vector.const 0 c) with
          | None => None
          | Some traces =>
           Some (fn  c traces)
        end
      |  just_set  fn to =>
         Some (fn c [ (any_trace pt)])
      | doc _ _ => None
    end.
  Fixpoint remove_none {c} {T: Type} (l:Vector.t (option T) c) :=
    match l with
        | [] => List.nil
        | l'::l'' => match l' with
                       | Some v => List.cons v (remove_none  l'')
                       | None => remove_none  l''
                     end
    end.
  
  Fixpoint vseq (from to:nat) :=
    match to with
      | O => []
      | S n => ( from) ::vseq (S from) n
    end.
  Compute (vseq 0 1).
Fixpoint findf {n} w p : option (component) := match w with
                        | a :: r =>
                          match a with
                            | just_set _ to as c
                            | watch_set _ _ _ to as c=>
                                                if beq_nat to p then
                                                  Some c
                                                else
                                                  findf r p
                            | doc _ _ => findf r p
                          end
                        | [] => None
                      end.
  Definition step {c n l} {w: wiring l} (pt :pintrace n c) :=
    let pindex := vseq 0 n in 
    let fns := map (findf w) pindex in
    let res := Vector.map (fun f => match f with Some c => next_value pt c | None => None end)  fns in
  update_trace pt res.

  Check step.
  (* Definition run' {n l} (w:wiring l) (pt: Vector.t (nat * Vector.t IO.t 0) n) : *)
  (*   Vector.t (nat * Vector.t IO.t 2) n := *)
  (*   step w (step w pt). *)

  Definition pin_trace_gen  {c} (w:Wires.wiring (S c)) :
    Vector.t (option (IO.trace 0)) (    (
                                          S (Vector.fold_left max  0 (pins w))

                                         ))
    :=
    let p := (pins w) in
    let m := Vector.fold_left max 0 p in
    let z := vseq 0 (S m) in
    Vector.map (fun p => match findf w p with | None => None | _ =>Some [] end ) z.

  Fixpoint run {l} (w:wiring (S l)) (fuel:nat):=
    match fuel with
        | O =>  (pin_trace_gen   w)
        | S n => @step _ _ (S l) w (run w n)
    end.
  
End IORUN.