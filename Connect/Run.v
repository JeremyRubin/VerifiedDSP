
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
Import ListNotations.
Require Import Arith.
Open Scope list_scope.
Require Import IOModule.


Require Import Wiring.

Module Wires := Wiring.Wiring.

Module IORUN.
  Import Wires.


  Definition pin_trace_gen w : list (nat* list IO.t):= map (fun p => (p, nil)) (pins w).
  Require Import Vector.
  Import VectorNotations.
  Fixpoint find_trace {c n:nat}  p pt  : option (Vector.t IO.t c) :=
    match pt with 
      | [] => None
      | (p', t)::rest => if beq_nat p' p then Some t else find_trace  p rest 
    end.
  Definition find_traces {c n pn:nat} (p :Vector.t nat pn)
             (pt :Vector.t (nat * Vector.t IO.t c) n)
  : option (Vector.t (Vector.t IO.t c) pn) :=
    let elts :=Vector.map (fun f =>  (find_trace f pt))  p in
    let none_missing := forallb (fun x => match x with | None => false | _ => true end ) (Vector.to_list elts) in
    if none_missing then 
      Some (Vector.map
              (fun f : option (Vector.t IO.t c) =>
                 match f with
                   | None => Vector.const 0 c
                   | Some x => x
                 end) elts)
    else None.

  Definition any_trace {c n:nat}  (pt :Vector.t (nat * Vector.t IO.t c) n ): Vector.t IO.t c:=
    match pt with 
      | [] => Vector.const 0 c
      | (p', t)::rest => t
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
  Fixpoint find_update {n:nat}  p (u: Vector.t (nat * IO.t) n)  : option (IO.t) :=
    match u with 
      | [] => None
      | (p', t)::rest => if beq_nat p' p then Some t else find_update  p rest 
    end.
  Definition update_trace {c n  n_u: nat} (pt:Vector.t (nat * Vector.t IO.t c) n)
             (u: Vector.t (nat * IO.t) n_u) :
             Vector.t  (nat * Vector.t IO.t (S c)) n :=

    map (fun pv:(nat * Vector.t IO.t c) => let (p, v) := pv in
                   match find_update p u with
                       | Some update => (p, update::v)
                       | None => (p, 0::v)
                   end) pt.

  Require Import Vector.
  Fixpoint next_value {c n} (pt: Vector.t (nat * Vector.t IO.t c) n)  w  :=
    match w with 
      | watch_set n from fn to =>
        match find_traces from pt with
          | None => None
          | Some traces =>
           Some (to, fn  c traces)
        end
      |  just_set  fn to =>
         Some (to, fn c [ (any_trace pt)])
      | doc _ _ => None
    end.
  Fixpoint remove_none {T: Type} (l:list (option T)) :=
    match l with
        | List.nil => List.nil
        | List.cons l' l'' => match l' with
                       | Some v => List.cons v (remove_none  l'')
                       | None => remove_none  l''
                     end
    end.
  Check next_value.
  Definition step {c n} w (pt : Vector.t (nat * Vector.t IO.t c) n) :=
    let v := (remove_none (List.map (next_value pt ) w)) in
  update_trace pt (of_list v).

  Check step.
  Definition run' {n } (w:wiring) (pt: Vector.t (nat * Vector.t IO.t 0) n) :
    Vector.t (nat * Vector.t IO.t 2) n :=
    step w (step w pt).

  Definition pin_trace_gen' {n: nat} (w: Vector.t nat n) : Vector.t (nat * Vector.t nat 0) n:=
    Vector.map (fun p:nat => (p, Vector.nil nat)) w.

  Fixpoint run w (fuel:nat):=
    match fuel with
        | O =>  (pin_trace_gen' (of_list (pins  w)))
        | S n => step w (run w n)
    end.
  
End IORUN.