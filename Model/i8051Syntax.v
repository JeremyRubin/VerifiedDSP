(* Copyright (c) 2011. Greg Morrisett, Gang Tan, Joseph Tassarotti, 
   Jean-Baptiste Tristan, and Edward Gan.

   This file is part of RockSalt.

   This file is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.
*)


(* This file provides abstract syntax definitions for the IA32 (x86) 32-bit
 * instruction set architecture. *)
Require Import List.
Require Import Bits.
Require Import ZArith.
Require Import Hex.
Set Implicit Arguments.
Local Open Scope Z_scope.

(********************************************)
(* Type definitions for x86 abstract syntax *)
(********************************************)
Definition zero_extend8_32(w:int8) : int8 := Word.repr (Word.unsigned w).
Definition sign_extend8_32(w:int8) : int8 := Word.repr (Word.signed w).
Definition zero_extend16_32(w:int8) : int8 := Word.repr (Word.unsigned w).
Definition sign_extend16_32(w:int8) : int8 := Word.repr (Word.signed w).
Definition port_number := int8.
Definition interrupt_type := int8.  
Definition selector := int16.  

Inductive register : Set := R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7.
Definition register_eq_dec : forall (x y:register), {x=y} + {x<>y}.
  intros ; decide equality.
Defined.

Definition Z_to_register(n:Z) := 
  match n with 
    | 0 => R0
    | 1 => R1
    | 2 => R2
    | 3 => R3 
    | 4 => R4 
    | 5 => R5 
    | 6 => R6
    | _ => R7
  end.

Definition register_to_Z   (r:register)  : Z :=
match r with 
 | R0 =>  0
 | R1 =>  1
 | R2 =>  2
 | R3 =>  3
 | R4 =>  4
 | R5 =>  5
 | R6 =>  6
 | R7 =>  7
 end.
Definition register_to_i  s (r:register)  : Word.int s :=
Word.repr (register_to_Z r).

Record address : Set := mkAddress {
  addrDisp : int8 ; 
  addrBase : option register ; 
  addrIndex : option (register)
}.
Inductive indirect : Set :=
 | ind_reg : register -> indirect.
 (* | ind_dptr : indirect *)
 (* | ind_a_dptr : indirect *)
 (* | ind_a_pc : indirect.                         *)
Inductive bitAddr : Set :=
  | bit_addr : forall (i : int8), bitAddr.
Module Alias.
  Definition C := bit_addr (Word.repr (hD0+7)).
  Definition AC := bit_addr (Word.repr (hD0+6)).
  Definition F0 := bit_addr (Word.repr (hD0+5)).
  Definition RS1 := bit_addr (Word.repr (hD0+4)).
  Definition RS0 := bit_addr (Word.repr (hD0+3)).
  Definition OV := bit_addr (Word.repr (hD0+2)).
  Definition P := bit_addr (Word.repr (hD0)).

  Definition P0 := h80.
  Definition P1 := h90.
  Definition P2 := hA0.
  Definition P3 := hB0.
  Definition ports := (P0,P1,P2,P3).


  Definition DPL := h82.
  Definition DPH := h83.
End Alias.
Inductive operand : Set := 
| Imm_op : int8 -> operand
| Reg_op : register -> operand
| Address_op : address -> operand
| Offset_op : int8 -> operand
| Acc_op : operand
| Direct_op : int8 -> operand
| Imm16_op : int16 -> operand
| Indirect_op : indirect -> operand
| Bit_op : bitAddr -> operand.

Inductive reg_or_immed : Set := 
| Reg_ri : register -> reg_or_immed
| Imm_ri : int8 -> reg_or_immed.

Inductive condition_type : Set :=
| O_ct (* overflow *)
| NO_ct (* not overflow *)
| B_ct (* below, not above or equal *)
| NB_ct (* not below, above or equal *)
| E_ct (* equal, zero *)
| NE_ct (* not equal, not zero *)
| BE_ct (* below or equal, not above *)
| NBE_ct (* not below or equal, above *)
| S_ct (* sign *)
| NS_ct (* not sign *)
| P_ct (* parity, parity even *)
| NP_ct (* not parity, parity odd *)
| L_ct  (* less than, not greater than or equal to *)
| NL_ct (* not less than, greater than or equal to *)
| LE_ct (* less than or equal to, not greater than *)
| NLE_ct (* not less than or equal to, greater than *).

Definition condition_type_eq_dec : 
  forall (x y:condition_type), {x=y} + {x<>y}.
  intros ; decide equality.
Defined.

Definition Z_to_condition_type(n:Z) : condition_type := 
  match n with 
    | 0 => O_ct
    | 1 => NO_ct
    | 2 => B_ct
    | 3 => NB_ct
    | 4 => E_ct
    | 5 => NE_ct
    | 6 => BE_ct
    | 7 => NBE_ct 
    | 8 => S_ct 
    | 9 => NS_ct 
    | 10 => P_ct
    | 11 => NP_ct 
    | 12 => L_ct 
    | 13 => NL_ct
    | 14 => LE_ct 
    | _ => NLE_ct
  end.

Inductive is_bit_op : operand -> Set :=
  | ibo : forall op, is_bit_op op.
Inductive instr : Set :=
(* two parts:  1-byte opcode instructions, followed by 2-byte in alphabetical order,
   following Table B-13 and Table ??? *) 
| ANL   : forall (op1 op2:operand), instr
| ADD   : forall (op1 op2:operand), instr
| SETB  : forall (op1:operand) , instr
| CLR   : forall (op1:operand), instr
| LJMP  : forall (op1:operand), instr
| JMP   : instr
| NOP   : instr.

(* Check SETB (ibo (Bit_op(bit_addr (Word.repr 0)))). *)
Inductive lock_or_rep : Set := lock | rep | repn.

Record prefix : Set := mkPrefix {
   lock_rep : option lock_or_rep;
   op_override : bool;
   addr_override : bool
}.


(* To add:

B.3.  MMX instructions
B.4.  Streaming SIMD instructions
B.5.  Floating point instructions

*)
