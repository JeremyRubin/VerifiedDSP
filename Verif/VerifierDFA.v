(* Copyright (c) 2011. Greg Morrisett, Gang Tan, Joseph Tassarotti, 
   Jean-Baptiste Tristan, and Edward Gan.

   This file is part of RockSalt.

   This file is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.
*)


(** VerifierDFA.v:  
    This file contains definitions of the parsers used to build the DFAs
    used in FastVerifier.
*)
Add LoadPath "../Model".
Require Import Coqlib.
Require Import Parser.
Require Import Ascii.
Require Import String.
Require Import List.
Require Import Bits.
Require Import Hex.
Require Import Decode.
Require Import Eqdep.
Require Import Int32.
Unset Automatic Introduction.
Set Implicit Arguments.
Open Scope char_scope.
Require ExtrOcamlString.
Require ExtrOcamlNatBigInt.
Require ExtrOcamlNatInt.
Import i8051_PARSER_ARG.
Import i8051_PARSER.
Import i8051_BASE_PARSER.

Require Import i8051Syntax.

(* In NaCl, ChunkSize is either 16 or 32 *)
Definition logChunkSize := 5%nat.
Definition chunkSize := two_power_nat logChunkSize.
Notation int8_of_nat n := (@repr 7 (Z_of_nat n)).
Definition safeMask := shl (Word.mone 7) (int8_of_nat logChunkSize).

Fixpoint int2bools_aux (bs : Z -> bool) (n: nat) : list bool :=
  match n with
    | O => bs 0 :: nil
    | S n' => bs (Z_of_nat n) :: int2bools_aux bs n'
  end.

Definition int_to_bools {s} (x: Word.int s) : list bool :=
  int2bools_aux (Word.bits_of_Z (s+1) (Word.unsigned x)) s.

Definition nat2bools(n:nat) : list bool := 
  let bs := Word.bits_of_Z 8 (Z_of_nat n) in
    (bs 7)::(bs 6)::(bs 5)::(bs 4)::(bs 3)::(bs 2)::(bs 1)::(bs 0)::nil.

Definition make_dfa t (p:parser t) := build_dfa 256 nat2bools 400 (par2rec p).
Implicit Arguments make_dfa [t].



Definition non_cflow_instrs : list (parser instruction_t) := 
    SETB_p::CLR_p::NOP_p::ANL_p::ADD_p::nil.

Definition instrs : list (parser instruction_t) := 
    LJMP_p::JMP_p::SETB_p::CLR_p::NOP_p::ANL_p::ADD_p::nil.
Definition non_cflow_instr i :=
  match i with
      | SETB _ | CLR _ | NOP  | ANL _ _ | ADD _ _ => true
      | _ => false
  end.
(** The list of valid prefix and instruction parsers for non-control-flow
    operations. *)

Definition non_cflow_parser := alts non_cflow_instrs.
Definition all_parsers := alts instrs.

Definition non_cflow_parser_list :=
  (List.map (fun (p:parser instruction_t) =>  p)
            non_cflow_instrs).
    (* Direct jumps. Destinations will be checked to see if 
   they are known, valid starts of instructions. *)

(* We only want to allow "near" jumps to direct, relative offsets *)

Definition dir_cflow : list (parser instruction_t) :=
 LJMP_p :: JMP_p ::nil. (* dir_near_JMP_p :: dir_near_Jcc_p :: dir_near_CALL_p :: nil.*)
Import i8051Syntax.
Lemma register_to_Z_identity1: forall r, Z_to_register (register_to_Z r) = r.
Proof. destruct r; auto.
Qed. 

Definition register_to_bools (r: register) := 
  let bs := Word.bits_of_Z 3 (register_to_Z r) in
    (bs 2) :: (bs 1) :: (bs 0) :: nil.

Fixpoint bitslist (bs: list bool) : parser unit_t :=
  match bs with
    | nil => Eps_p
    | b::bs' => Cat_p (Char_p b) (bitslist bs') @ (fun _ => tt %% unit_t)
  end.

Fixpoint bitslist' (bs: list bool) : string :=
  match bs with
    | nil => EmptyString
    | true::bs' => append "1" (bitslist' bs')
    | false::bs' => append "0" (bitslist' bs')
  end.

Definition b8 := true::false::false::false::nil.
Definition b3 := false::false::true::true::nil.
Definition be := true::true::true::false::nil.
Definition b0 := false::false::false::false::nil.
Definition bf := true::true::true::true::nil.

Definition mybits := b8 ++ b3 ++ be ++ b0 ++ be ++ b0 ++ bf ++ bf ++ be ++ b0.


(* These are akin to the NaCl "pseudo-instruction" nacljmp. We will
   check if the jump destination is appropriately masked by the
   preceding AND *)

  Fixpoint parseloop ps bytes := 
    match bytes with 
      | nil => None
      | b::bs => match Decode.i8051_PARSER.parse_byte ps b with 
                   | (ps', nil) => parseloop ps' bs
                     (* JGM: FIX!  What to do with prefix? *)
                   | (ps',(LJMP  (Imm_op disp) )::_) => 
                     match bs with 
                       | nil => Some disp
                       | _ => None
                     end
                   | (ps', _) => None
                 end
    end.

(** Next, we define a boolean-valued test that tells whether an instruction
    is a valid non-control-flow instruction.  We should have the property
    that the [non_cflow_parser] only builds instructions that satisfy this
    predicate (as shown below.)  Furthermore, we should be able to argue
    that for each of these instructions, the NaCL SFI invariants are preserved. 
*)
Definition no_imm_op(op1:operand) : bool := 
  match op1 with 
    | Imm_op _ => false
    | _ => true
  end.


Definition no_prefix (p : prefix) : bool :=  true.

(** We rule out JMPs and CALLs that are far (i.e., not near), that
    are absolute instead of relative, that don't have an immediate
    operand, or that have a selector. *)
Definition dir_cflow_instr (pre:prefix) (ins: instr) : bool :=
  match ins with
    | LJMP (Imm_op _)  => true
    | _ => false
  end.

(** This predicate is defined on a pair of prefixes and instructions and
    captures the legal masked indirect jumps. *)
Definition nacljmp_mask_instr (pfx1:prefix) (ins1:instr) (pfx2:prefix) (ins2:instr) :=
  no_prefix pfx1 && no_prefix pfx2 && 
  match ins1 with
    | ANL (Reg_op r1) (Imm_op wd) => 
      zeq (Word.signed wd) (Word.signed safeMask) &&
      (if register_eq_dec r1 r1 then false else true)
    | _ => false
  end.
Definition nacl_MASK_p : parser (pair_t instruction_t instruction_t):=
  let imMask := (Imm_op (Word.repr hF0)) in
  ( bits ("01010100"++"11110000") @ (fun _ => ANL Acc_op imMask %% instruction_t))
    $ (("01010011") $$ bitslist' (int_to_bools (@Word.repr 7 Alias.DPL)) $$ bits "11110000" @ (fun _ => ANL (Direct_op (Word.repr Alias.DPL)) imMask %% instruction_t)).

Definition nacl_JMP_p  :=
  JMP_p.
  
Definition nacljmp_p  :
  parser (pair_t (pair_t instruction_t instruction_t) instruction_t) :=
    nacl_MASK_p $ (nacl_JMP_p).
Definition nacljmp_mask :
  list (parser (pair_t (pair_t instruction_t instruction_t) instruction_t))
  := nacljmp_p :: nil.
 

Definition dfas := (make_dfa non_cflow_parser, make_dfa (alts dir_cflow), make_dfa (alts nacljmp_mask)).
(* Extraction "tables.ml" dfas.*)


