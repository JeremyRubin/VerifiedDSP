
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
Require Import List.
Import ListNotations.
Open Scope list_scope.
Require Import String.
Require Import Run.
Require Import IOModule.
Import IO.
Import Wires.
Open Scope wiring_scope.
Add LoadPath "../Model".
Require Import Bits.
Require Import ZArith.
Require Import i8051Semantics.
Require Import i8051Syntax.
Import i8051_MACHINE.
(* Definition default := {| executing := NOP; *)
(*                          pc := Word.repr 0; *)
(*                          cycle := 0; *)
(*                          output := {| P0:=Word.repr 0;P1:=Word.repr 0;P2:=Word.repr 0;P3:=Word.repr 0 |} *)
(*                       |}. *)
Definition m_init   :=  {|
                        pc_reg := Word.zero;
                        pc_mod := Word.zero;
                        (* trace := []; *)
                        external :=
                          {| P0:=Word.zero;P1:=Word.zero;P2:=Word.zero;P3:=Word.zero |}|}.

(*     (fun tr => let t := hd  default tr in  *)
(*                         {| executing := executing t; *)
(*                            pc := pc t; *)
(*                            cycle := cycle t; *)
(*                            output := {| P0:=Word.repr 0;P1:=Word.repr 0;P2:=Word.repr 0;P3:=Word.repr 0 |} *)

(*                         |}) *)
(* |}. *)
Import i8051_RTL.
Definition oracle := {|
                      oracle_bits := Word.repr ; 
                      oracle_offset := 0
                    |}.
Definition r := {|
                 rtl_oracle := oracle ; 
                 rtl_env := empty_env ; 
                 rtl_mach_state := m_init; 
                 rtl_memory := AddrMap.init (Word.repr 0);
                 rtl_code := CodeMap.init (Word.repr 0)
               |}. 

Module i8051_Component.
  (* Variable threshold : nat. *)
  Definition threshold := 1.
  Definition tighter {n} (x : Vector.t (Vector.t IO.t (S n)) 1) threshold := 
                    match threshold - (Vector.hd (Vector.hd  x)) with
                      | 0 => 1
                      | _ => 0
                    end.
  Definition digitizer : IO.func 1:=
    fun c=>  (fun x =>  
                match x with
                  | (Vector.cons  (Vector.cons r _ l) 0 Vector.nil) as V  => tighter V threshold
                  | _ => 0
                end).
  Require Import Vector.
  Import Vector.
  Import VectorNotations.
  Definition nilwiring : Wires.wiring 0:= [].
  Definition digitize'  (from to: Wires.pin): Wires.wiring (2) :=
    nilwiring // [from] ~> digitizer ~> to # to ("Digitized Pin").

  (* Check @fold_left. *)
  (* Fixpoint digitize {c : nat}  (from to:Vector.t (Wires.pin)c) : *)
  (*   let d := map2 digitize' from to in *)
  (*   @fold_left _ _ append [] d. *)
  (*   Wires.wiring (l+c+c) := fold_left2 digitize' from to. *)
    (* match v in Vector.t _ s return match s with |O => True |S n => Wires.wiring (l+s+s) end with *)
    (*   | [] => I *)
    (*   | (from, to) :: r => digitize (digitize' w to from) r *)
    (* end. *)

  (* Definition mk8051 (code:string) (pinmap:list (nat * nat)) := *)

  
  Definition porttrace c := Vector.t ports c.
  Definition run_8051 { c} init (ps:porttrace c) := Run8051.dump_state  {|
                                                    rtl_oracle :=  {|
                                                                   oracle_bits := Word.repr ; 
                                                                   oracle_offset := 0
                                                                 |}; 
                                                    rtl_env := empty_env ; 
                                                    rtl_mach_state := m_init; 
                                                    rtl_memory := AddrMap.init (Word.repr 0);
                                                    rtl_code := CodeMap.init (Word.repr 0)
                                                  |} ps init.
  (* Definition computeitIHXString cycle init :=  *)
  (*   let loads := flat_map (fun x => *)
  (*                            match ihx_to_byte_assoc_line (asciis x) None (Some nil) with *)
  (*                              | Some v => v *)
  (*                              | None => nil *)
  (*                            end) init in *)
  (*  run8051 cycle  (load_code_bytes loads). *)
  Definition run_8051_bin_string {c} bin (ps:porttrace c) := 
    run_8051 (load_code_bytes_bin bin 0) ps.
  Definition condense (b7 b6 b5 b4 b3 b2 b1 b0: bool) :=
    let i7 : int8 := Word.bool_to_int b7 in
    let i6 : int8 := Word.bool_to_int b6 in
    let i5 : int8 := Word.bool_to_int b5 in
    let i4 : int8 := Word.bool_to_int b4 in
    let i3 : int8 := Word.bool_to_int b3 in
    let i2 : int8 := Word.bool_to_int b2 in
    let i1 : int8 := Word.bool_to_int b1 in
    let i0 : int8 := Word.bool_to_int b0 in
    fold_left (fun s f => Word.or (Word.shl s (Word.repr 1))  f) Word.zero [i7;i6;i5;i4;i3;i2;i1;i0].

  Require Import Vector.
  Import VectorNotations.
  Import Vector.

  (* Definition map {A} {B} (f : A->A->A->A->A->A->A->A -> B) : *)
  (*   forall {n} (l7 l6 l5 l4 l3 l2 l1 l0: t A n), t B n := *)
  (*   fix map_fix {n} (l7 l6 l5 l4 l3 l2 l1 l0 : t A n) : t B n := *)
  (*   match l7, l6, l5, l4, l3, l2, l1, l0  with *)
  (*     | a::a',b::b',c::c',d::d',e::e',f::f',g::g',h::h' => *)
  (*       (f a b c d e f g h) :: (map_fix a' b' c' d' e' f' g' h') *)
  (*     | _,_,_,_,_,_,_,_ => [] *)
  (*   end. *)

  (*   match v with *)
  (*                                            | [] => [] *)
  (*                                            | a :: v' => (f a) :: (map_fix v') *)
  (*                                          end. *)

      (* | a::b::c::d::e::f::g::h::i::j => I *)
      (* | a::b::c::d::e::f::g::[] => I *)
      (* | a::b::c::d::e::f::[]=> I *)
      (* | a::b::c::d::e::[] => I *)
      (* | a::b::c::d::[] => I *)
      (* | a::b::c::[] => I *)
      (* | a::b::[] => I *)
      (* | a::[] => I *)
  Definition get8th {A} (v:Vector.t A 8) : A:=
    hd (tl (tl (tl (tl (tl (tl (tl v))))))).
  Definition get7th {A} (v:Vector.t A 8) : A:=
    hd (tl (tl (tl (tl (tl (tl v)))))).
  Definition get6th {A} (v:Vector.t A 8) : A:=
    hd (tl (tl (tl (tl (tl v))))).

  Definition get5th {A} (v:Vector.t A 8) : A:=
    hd  (tl (tl (tl (tl v)))).

  Definition get4th {A} (v:Vector.t A 8) : A:=
    hd  (tl (tl (tl v))).

  Definition get3rd {A} (v:Vector.t A 8) : A:=
    hd  (tl (tl v)).

  Definition get2nd {A} (v:Vector.t A 8) : A:=
    hd  (tl v).

  Definition get1st {A} (v:Vector.t A 8) : A:=
    hd  v.
  Definition condense' {n} (v' : Vector.t (Vector.t bool n) 8) :=  (* Vector.t int8 n:= *)

    let v2 := Vector.map (Vector.map (fun f:bool => if f then Word.one else @Word.zero 7)) v' in
    let v := Vector.map2 (fun f1 f2 => Vector.map (fun f => Word.shl f (Word.repr (Z_of_nat f2))) f1) v2 (of_list (seq 0 8)) in
    (* match v  in Vector.t _ n' return ( match  n'  with *)
    (*                                     |0 => unit *)
    (*                                     |1=>unit *)
    (*                                     |2 => unit *)
    (*                                     |3=> unit *)
    (*                                     |4=> unit *)
    (*                                     |5=> unit *)
    (*                                     | 6 => unit *)
    (*                                     |7 => unit *)
    (*                                     | S(S(S(S(S(S(S(S(S n)))))))) => unit *)
    (*                                     | 8 => Vector.t int8 n' *)
    (*                                      end) with *)
    (*   | [] => tt   *)
    (*   | [_] => tt   *)
    (*   | [_;_;_] => tt   *)
    (*   | [_;_;_;_] => tt   *)
    (*   | [_;_;_;_;_] => tt   *)
    (*   | [_;_;_;_;_;_] => tt   *)
    (*   | [_;_;_;_;_;_;_] => tt   *)
    (*   | [_;_;_;_;_;_;_;_] => tt   *)
    (*   | a::b::c::d::e::f::g::h::i::_ => a *)
    (*   | a::b::c::d::e::f::g::h::[] => a *)
    (*   end. *)
    let l7 := get8th v in
    let l6 := get7th v in
    let l5 := get6th v in
    let l4 := get5th v in
    let l3 := get4th v in
    let l2 := get3rd v in
    let l1 := get2nd v in
    let l0 := get1st v in
    let or := Vector.map2 (fun f1 f2 => Word.or f1 f2) in
    let a0 := or l0 l1 in
    let a1 := or l2 l3 in
    let a2 := or l4 l5 in
    let a3 := or l6 l7 in
    let a4 := or a0 a1 in
    let a5 := or a2 a3 in
    or a4 a5 .



  (* match v  as f in (Vector.t _ eight) *)
  (*         return (match  eight with *)
  (*                   | 8 => Vector.t int8 n *)
  (*                   | _ => True *)
  (*                 end) with *)
  (*     (* | [a::a';b::b';c::c';d::d';e::e';f::f';g::g';h::h'] => *) *)
  (*     (*   (* Vector.nil int8 *) *) *)
  (*     (*   (condense a b c d e f g h)::(condense' a' b' c' d' e' f' g' h') *) *)
  (*     (* | a::b::c::d::e::f::g::h::[] => Vector.nil int8 *) *)
  (*     | map *)
  (*     | _ => I *)
  (*   end. *)
  
  Fixpoint to_trace {n} (p0 p1 p2 p3: Vector.t int8 n) :=
    let m := Vector.map2
               (fun p0 p1 => {| P0 := p0; P1 := p1; P2:=Word.zero;P3:=Word.zero |}) p0 p1 in 
    let m' := Vector.map2 (fun p2 m' => {| P0 := P0 m'; P1 := P1 m'; P2:=p2;P3:= Word.zero |}) p2 m in
    Vector.map2 (fun p3 m'' => {| P0 := P0 m''; P1 := P1 m''; P2:=P2 m'';P3:= p3 |}) p3 m'.

  Definition traces {c} (tr:IO.traces 32 c) thresh :=
    let f := Vector.map (Vector.map (fun x => NPeano.ltb x thresh)) in
    let digitized := ( f tr) in
    match digitized with
        |(p00::p01::p02::p03::p04::p05::p06::p07::
           p10::p11::p12::p13::p14::p15::p16::p17::
           p20::p21::p22::p23::p24::p25::p26::p27::
           p30::p31::p32::p33::p34::p35::p36::p37::[]) =>
         
        to_trace (condense' [p07;p06; p05; p04; p03; p02; p01; p00])
         (condense' [p17; p16; p15; p14; p13; p12; p11; p10])
         (condense' [p27; p26; p25; p24; p23; p22; p21; p20])
         (condense' [p37; p36; p35; p34; p33; p32; p31; p30] )
         (* How can I show this term irrelevant? *)
        |_ => Vector.const {| P0:=Word.zero ; P1 := Word.zero; P2 := Word.zero; P3 := Word.zero |} c
    end.
        

    

    
  Definition i8051_Component bin threshold (conv: option ports -> nat):
    IO.func 32 := fun {c} (t:IO.traces 32 c) =>
                    let ps := traces t threshold in
                    conv (run_8051_bin_string bin ps).
  
  Require Import Ascii.
  Definition conv_char (c:ascii) : int8 := Word.repr (Z_of_nat (nat_of_ascii c)).
Check i8051_Component.
End i8051_Component.
Import i8051_Component.
Definition dac x := match x with
					  | Some v =>
						let z := P3 v in
						N.to_nat(    Z.to_N (Word.unsigned (Word.and z (Word.not (Word.repr 1)))))
                      | None => 0
                    end.