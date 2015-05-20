
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
  Search nat.
  Definition digitizer : IO.func 1:=
    (fun x =>
                    match threshold - (hd 0 (Vector.hd  x)) with
                      | 0 => 1
                      | _ => 0
                    end).
  Fixpoint digitize l acc :=
    match l with
      | (a, b) :: r => digitize r (acc // a ~> digitizer  ~> b # b ("Digitized Port"))
      | [] => acc
    end.

  (* Definition mk8051 (code:string) (pinmap:list (nat * nat)) := *)

  

  Definition run_8051 init ps := dump_state  {|
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
  Definition run_8051_bin_string bin ps := 
    run_8051 (load_code_bytes_bin bin 0) ps.
  SearchAbout nat.
  SearchAbout Word.int.
  Definition condense (b7 b6 b5 b4 b3 b2 b1 b0: bool) :=
    let i7 : int8 := Word.bool_to_int b7 in
    let i6 : int8 := Word.bool_to_int b6 in
    let i5 : int8 := Word.bool_to_int b5 in
    let i4 : int8 := Word.bool_to_int b4 in
    let i3 : int8 := Word.bool_to_int b3 in
    let i2 : int8 := Word.bool_to_int b2 in
    let i1 : int8 := Word.bool_to_int b1 in
    let i0 : int8 := Word.bool_to_int b0 in
    fold_left (fun s f => Word.or (Word.shl s (Word.repr 1))  f) [i7;i6;i5;i4;i3;i2;i1;i0] Word.zero.

  Fixpoint condense' l7 l6 l5 l4 l3 l2 l1 l0 :=
    match l7, l6, l5, l4, l3, l2, l1, l0  with
        | a::a',b::b',c::c',d::d',e::e',f::f',g::g',h::h' => (condense a b c d e f g h) :: (condense' a' b' c' d' e' f' g' h')
        | _,_,_,_,_,_,_,_ => []
    end.
  
  Fixpoint to_trace p1 p2 p3 p4 :=
    match p1, p2, p3, p4 with
      | a::a', b::b', c::c', d::d' => {| P0 := a; P1 := b; P2:=c;P3:=d |} :: to_trace a' b' c' d'
      | _,_,_,_ => []
    end.

  Require Import Vector.
  Import VectorNotations.
  Import Vector.
  Require Import Fin.
  Import Fin.
  Close Scope vector_scope.
  Open  Scope list_scope.
  Definition traces (tr:Vector.t (list nat) 32) thresh :=
    let f := Vector.map (List.map (fun x => NPeano.ltb x thresh)) in
    let digitized := to_list( f tr) in
    

    match digitized with
        |(p00::p01::p02::p03::p04::p05::p06::p07::
           p10::p11::p12::p13::p14::p15::p16::p17::
           p20::p21::p22::p23::p24::p25::p26::p27::
           p30::p31::p32::p33::p34::p35::p36::p37::List.nil) =>
         
        to_trace (condense' p07 p06 p05 p04 p03 p02 p01 p00)
         (condense' p17 p16 p15 p14 p13 p12 p11 p10)
         (condense' p27 p26 p25 p24 p23 p22 p21 p20)
         (condense' p37 p36 p35 p34 p33 p32 p31 p30)
        |_ => List.nil
    end.
        

    

    
  Definition i8051_Component bin threshold (conv: option ports -> nat):= (fun t =>
                     let ps := traces t threshold in
                     conv (run_8051_bin_string bin ps)).
  
  Require Import Ascii.
  Definition conv_char (c:ascii) : int8 := Word.repr (Z_of_nat (nat_of_ascii c)).
Check i8051_Component.
End i8051_Component.
Compute (seq 0 32).
Import i8051_Component.
SearchAbout Word.int.
Check Z.to_N.
Search nat.
Definition dac x := match x with
					  | Some v =>
						let z := P3 v in
						N.to_nat(    Z.to_N (Word.unsigned (Word.and z (Word.not (Word.repr 1)))))
                      | None => 0
                    end.
Check dac.