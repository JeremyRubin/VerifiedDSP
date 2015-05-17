(* Copyright (c) 2011. Greg Morrisett, Gang Tan, Joseph Tassarotti, 
   Jean-Baptiste Tristan, and Edward Gan.

   This file is part of RockSalt.

   This file is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.
*)

(* This file provides simple bit-level parsing combinators for disassembling
 * Intel IA32 (x86) 32-bit binaries. *)
Require Coqlib.
Require Import Coq.Init.Logic.
Require Import Bool.
Require Import List.
Require Import String.
Require Import Maps.
Require Import Ascii.
Require Import ZArith.
Require Import Eqdep.
Require Import Parser.
Unset Automatic Introduction.
Set Implicit Arguments.
Local Open Scope Z_scope.


Require ExtrOcamlString.
Require ExtrOcamlNatBigInt.


(* a module for generating the parser for x86 instructions *)
Module i8051_PARSER_ARG.
  Require Import i8051Syntax.
  Require Import Bits.
  
  Definition char_p : Set := bool.
  Definition char_eq : forall (c1 c2:char_p), {c1=c2}+{c1<>c2} := bool_dec.
  Inductive type : Set := 
  | Int_t : type
  | Byte_t : type
  | Operand_t : type
  | Instruction_t : type
  | Prefix_t : type.

  Definition tipe := type.
  Definition tipe_eq : forall (t1 t2:tipe), {t1=t2} + {t1<>t2}.
    intros ; decide equality.
  Defined.

  Fixpoint tipe_m (t:tipe) := 
    match t with 
      | Int_t => Z
      | Byte_t => int8
      | Operand_t => operand
      | Instruction_t => instr
      | Prefix_t => prefix
    end.
End i8051_PARSER_ARG.

Module i8051_PARSER.
  Module i8051_BASE_PARSER := Parser.Parser(i8051_PARSER_ARG).
  Require Import i8051Syntax.
  Require Import Bits.
  Import i8051_PARSER_ARG.
  Import i8051_BASE_PARSER.

  Definition int_t := tipe_t Int_t.
  Definition register_t := tipe_t Operand_t.
  Definition byte_t := tipe_t Byte_t.
  Definition operand_t := tipe_t Operand_t.
  Definition instruction_t := tipe_t Instruction_t.
  Definition prefix_t := tipe_t Prefix_t.
  (* combinators for building parsers *)
  Definition bit(x:bool) : parser char_t := Char_p x.
  Definition never t : parser t := Zero_p t.
  Definition always t (x:result_m t) : parser t := @Map_p unit_t t (fun (_:unit) => x) Eps_p.
  Definition alt t (p1 p2:parser t) : parser t := Alt_p p1 p2.
  Definition alts t (ps: list (parser t)) : parser t := List.fold_right (@alt t) (@never t) ps.
  Definition map t1 t2 (p:parser t1) (f:result_m t1 -> result_m t2) : parser t2 := 
    @Map_p t1 t2 f p.
  Implicit Arguments map [t1 t2].
  Definition seq t1 t2 (p1:parser t1) (p2:parser t2) : parser (pair_t t1 t2) := Cat_p p1 p2.
  Definition cons t (pair : result_m (pair_t t (list_t t))) : result_m (list_t t) := 
    (fst pair)::(snd pair).
  Definition seqs t (ps:list (parser t)) : parser (list_t t) := 
    List.fold_right (fun p1 p2 => map (seq p1 p2) (@cons t)) 
      (@always (list_t t) (@nil (result_m t))) ps.
  Fixpoint string_to_bool_list (s:string) : list bool := 
    match s with
      | EmptyString => nil
      | String a s => 
        (if ascii_dec a "0"%char then false else true)::(string_to_bool_list s)
    end.

  Fixpoint bits_n (n:nat) : result := 
    match n with 
      | 0%nat => unit_t
      | S n => pair_t char_t (bits_n n)
    end.
  Fixpoint field'(n:nat) : parser (bits_n n) := 
    match n with 
      | 0%nat => Eps_p
      | S n => Cat_p Any_p (field' n)
    end.
  Fixpoint bits2Z(n:nat)(a:Z) : result_m (bits_n n) -> result_m int_t := 
    match n with 
      | 0%nat => fun _ => a
      | S n => fun p => bits2Z n (2*a + (if (fst p) then 1 else 0)) (snd p)
    end.
  Definition bits2int(n:nat)(bs:result_m (bits_n n)) : result_m int_t := bits2Z n 0 bs.
  Fixpoint bits (x:string) : parser (bits_n (String.length x)) := 
    match x with 
      | EmptyString => Eps_p
      | String c s => 
        (Cat_p (Char_p (if ascii_dec c "0"%char then false else true)) (bits s))
    end.

  (* notation for building parsers *)
  Infix "|+|" := alt (right associativity, at level 80).
  Infix "$" := seq (right associativity, at level 70).
  Infix "@" := map (right associativity, at level 75).
  Notation "e %% t" := (e : result_m t) (at level 80).
  Definition bitsleft t (s:string)(p:parser t) : parser t := 
    bits s $ p @ (@snd _ _).
  Infix "$$" := bitsleft (right associativity, at level 70).

  Definition anybit : parser char_t := Any_p.
  Definition field(n:nat) := (field' n) @ (bits2int n).
  Definition reg := (field 3) @ ((fun r => Reg_op (Z_to_register r)) : _ -> result_m operand_t).
  Definition direct := (field 8) @ ((fun r => Direct_op (@Word.repr 7 r)) : _ -> result_m operand_t).
  Definition immediate := (field 8) @ ((fun r => Imm_op (@Word.repr 7 r)) : _ -> result_m operand_t).

  Definition immediate_16 := (field 16) @ ((fun r => Imm16_op (@Word.repr 15 r)) : _ -> result_m operand_t).
  Definition bit_address := (field 8) @ ((fun r => Bit_op (bit_addr (@Word.repr 7 r))) : _ -> result_m operand_t).
  Definition byte := (field 8) @ (@Word.repr 7 : _ -> result_m byte_t).
 (* Definition halfword := (field 16) @ (@Word.repr 15 : _ -> result_m half_t).
  Definition word := (field 32) @ (@Word.repr 31 : _ -> result_m word_t). *)
  Definition halfword := byte .
  Definition word := byte .

  (* This is used in a strange edge-case for modrm parsing. See the
     footnotes on p37 of the manual in the repo This is a case where I
     think intersections/complements would be nice operators *)

  (* JGM: we can handle this in the semantic action instead of the parser, 
     so I replaced si, which used this and another pattern for [bits "100"]
     to the simpler case below -- helps to avoid some explosions in the 
     definitions. *)


      
  (* These next 4 parsers are used in the definition of the mod/rm parser *)

  (* Parsers for the individual instructions *)

  Definition arith_p_with_direct opcode base := base $$ 
                             (
                               ("1" $$ reg) @ (fun r => opcode Acc_op r %% instruction_t)
                                |+| "0101" $$ direct @ (fun r => opcode Acc_op r %% instruction_t)
                                |+| "011" $$ anybit  @ (fun b => let r := if b then R1 else R0 in
                                                                  opcode Acc_op (Indirect_op (ind_reg r)) %% instruction_t)
                                |+| "0100" $$ immediate @ (fun i => opcode Acc_op i %% instruction_t)

                                |+| "0010" $$ direct @ (fun d => opcode Acc_op d %% instruction_t)
                                |+| "0011" $$ direct $ immediate @
                                (fun di =>
                                   match di with
                                     | (d, i) => opcode d i %% instruction_t
                                   end)).

  Definition arith_p opcode base := base $$ 
                             (
                               ("1" $$ reg) @ (fun r => opcode Acc_op r %% instruction_t)
                                |+| "0101" $$ direct @ (fun r => opcode Acc_op r %% instruction_t)
                                |+| "011" $$ anybit  @ (fun b => let r := if b then R1 else R0 in
                                                                  opcode Acc_op (Indirect_op (ind_reg r)) %% instruction_t)
                                |+| "0100" $$ immediate @ (fun i => opcode Acc_op i %% instruction_t)).

  Definition ANL_p := arith_p_with_direct ANL "0101".
  Definition ADD_p := arith_p ADD "0010".

  Definition bitwise_p pre op := pre $$ (
                             bits "0011" @ (fun _ => op (Bit_op Alias.C) %% instruction_t)
                                    |+| "0010"  $$ bit_address @ (fun i => op i %% instruction_t)).
  Definition SETB_p := bitwise_p "1101" SETB.
  Definition CLR_p := bits "11100100" @ (fun _ => CLR Acc_op %% instruction_t)
                           |+| bitwise_p "1100" CLR.
  Definition NOP_p := bits "00000000" @ (fun _ =>  NOP %% instruction_t).
  (* Now glue all of the individual instruction parsers together into 
     one big parser. *)
  Definition LJMP_p := "00000010" $$ immediate_16 @ (fun a => LJMP a %%instruction_t).
  Definition JMP_p := bits "01110011" @ (fun _ => JMP %% instruction_t).
  Definition instrs : list (parser instruction_t) :=
    JMP_p::SETB_p::CLR_p::LJMP_p::NOP_p::ANL_p::ADD_p::nil.

  Fixpoint list2pair_t (l: list result) :=
    match l with
      | nil => unit_t
      | r::r'::nil => pair_t r r'
      | r::l' => pair_t r (list2pair_t l')
    end.
 


  (* Ok, now I want all permutations of the above four parsers. 
     I make a little perm2 combinator that takes two parsers and gives you
     p1 $ p2 |+| p2 $ p1, making sure to swap the results in the second case *)
  
  Definition perm2 t1 t2 (p1: parser t1) (p2: parser t2) : parser (pair_t t1 t2) :=
      p1 $ p2 |+|
      p2 $ p1 @ (fun p => match p with (a, b) => (b, a) %% pair_t t1 t2 end).

  (* Then I build that up into a perm3 and perm4. One could make a recursive
     function to do this, but I didn't want to bother with the necessary
     proofs and type-system juggling.*) 

  Definition perm3 t1 t2 t3 (p1: parser t1) (p2: parser t2) (p3: parser t3)
    : parser (pair_t t1 (pair_t t2 t3)) :=
    let r_t := pair_t t1 (pair_t t2 t3) in
       p1 $ (perm2 p2 p3)
   |+| p2 $ (perm2 p1 p3) @ (fun p => match p with (b, (a, c)) => (a, (b, c)) %% r_t end)
   |+| p3 $ (perm2 p1 p2) @ (fun p => match p with (c, (a, b)) => (a, (b, c)) %% r_t end).

  Definition perm4 t1 t2 t3 t4 (p1: parser t1) (p2: parser t2) (p3: parser t3)
    (p4: parser t4) : parser (pair_t t1 (pair_t t2 (pair_t t3 t4))) :=
    let r_t := pair_t t1 (pair_t t2 (pair_t t3 t4)) in
       p1 $ (perm3 p2 p3 p4)
   |+| p2 $ (perm3 p1 p3 p4) @ 
         (fun p => match p with (b, (a, (c, d))) => (a, (b, (c, d))) %% r_t end)
   |+| p3 $ (perm3 p1 p2 p4) @ 
         (fun p => match p with (c, (a, (b, d))) => (a, (b, (c, d))) %% r_t end)
   |+| p4 $ (perm3 p1 p2 p3) @ 
         (fun p => match p with (d, (a, (b, c))) => (a, (b, (c, d))) %% r_t end). 

  (* In this case, prefixes are optional. Before, each of the above
     parsing rules for the prefixes accepted Eps, and this was how we
     handled this.  However, if the parsers you join with perm can
     each accept Eps, then the result is a _highly_ ambiguous parser.

     Instead we have a different combinator, called option_perm, that 
     handles this without introducing extra ambiguity *)

  (* This signature is slightly awkward - because there's no result
     type corresponding to option (and I'm hesitant to add it to
     Parser at the moment) we can't just have a signature like parser
     t1 -> parser t2 -> parser (option_t t1) (option_t t2)) *)
    

                                      
  Definition opt2b (a: option bool) (default: bool) :=
    match a with
      | Some b => b
      | None => default
    end.
  
  Definition instruction_parser_list := 
      instrs.

  Definition instruction_parser := alts instruction_parser_list.

  Definition instruction_regexp_pair := parser2regexp instruction_parser.
  Record instParserState := mkPS { 
    inst_ctxt : ctxt_t ; 
    inst_regexp : regexp (instruction_t) ; 
    inst_regexp_wf : wf_regexp inst_ctxt inst_regexp 
  }.

  Definition initial_parser_state : instParserState := 
    mkPS (snd instruction_regexp_pair) (fst instruction_regexp_pair) 
    (p2r_wf instruction_parser _).

  Definition byte_explode (b:int8) : list bool := 
  let bs := Word.bits_of_Z 8 (Word.unsigned b) in
    (bs 7)::(bs 6)::(bs 5)::(bs 4)::(bs 3)::(bs 2)::(bs 1)::(bs 0)::nil.

  Definition parse_byte (ps:instParserState) (b:int8) : 
    instParserState * list ( instr) := 
    let cs := byte_explode b in
    let r' := deriv_parse' (inst_regexp ps) cs in
    let wf' := wf_derivs (inst_ctxt ps) cs (inst_regexp ps) (inst_regexp_wf ps) in
      (mkPS (inst_ctxt ps) r' wf', apply_null (inst_ctxt ps) r' wf').

End i8051_PARSER.

