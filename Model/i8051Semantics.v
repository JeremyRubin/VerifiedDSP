(* Copyright (c) 2011. Greg Morrisett, Gang Tan, Joseph Tassarotti, 
   Jean-Baptiste Tristan, and Edward Gan.

   This file is part of RockSalt.

   This file is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.
*)

Require ExtrOcamlString.
Require ExtrOcamlNatBigInt.
Require ExtrOcamlZBigInt.
Require Import List.
Require Import Bits.
Require Import ZArith.
Require Import Parser.
Require Import Decode.
Require Import String.
Require Import Monad.
Require Import Maps.
Require Import i8051Syntax.
Require Import Hex.
Require Import RTL.
Set Implicit Arguments.
Unset Automatic Introduction.

Module i8051_MACHINE.
  Local Open Scope Z_scope.
  Local Open Scope string_scope.

  Definition size_addr := size8.
  Definition size_pc := size16.

  Inductive regbank : Set :=
    |bank_zero : regbank
    |bank_one :regbank
    | bank_two :regbank
                 | bank_three : regbank.
  Definition bits_to_bank  (hi lo:bool) :=
    match (hi, lo) with
      | (true, true) =>  bank_zero
      | (true, false) => bank_one
      | (false, true) => bank_two
      | (false, false) => bank_three
    end.
  Definition bank_to_offset (b: regbank) : Word.int size_addr :=
    Word.repr (match b with
      |bank_zero => 0
      |bank_one =>8
      |bank_two =>16
      |bank_three => 24
    end).
  Inductive loc : nat -> Set := 
  | pc_loc : loc size_pc.

  Inductive ploc : nat -> Set :=
  | ram_loc : register -> ploc size8.

  Definition location := loc.

  Definition fmap (A B:Type) := A -> B.
  Definition upd A (eq_dec:forall (x y:A),{x=y}+{x<>y}) B (f:fmap A B) (x:A) (v:B) : 
    fmap A B := fun y => if eq_dec x y then v else f y.
  Definition look A B (f:fmap A B) (x:A) : B := f x.

  Record mach := { 
    pc_reg : int size_pc
  }.
  Definition mach_state := mach.

  Definition get_location s (l:loc s) (m:mach_state) : int s := 
    match l in loc s' return int s' with 
      | pc_loc => pc_reg m
    end.


  Definition set_pc v  :=  {|
       pc_reg := v
    |}.

  Definition set_location s (l:loc s) (v:int s) (m:mach_state) := 
    match l in loc s' return int s' -> mach_state with 
      | pc_loc => fun v => set_pc v
    end v.
End i8051_MACHINE.

Module i8051_RTL := RTL.RTL(i8051_MACHINE).

Module i8051_Decode.
  Import i8051_MACHINE.
  Import i8051_RTL.
  Local Open Scope monad_scope.
  Record conv_state := { c_rev_i : list rtl_instr ; c_next : Z }.
  Definition Conv(T:Type) := conv_state -> T * conv_state.
  Instance Conv_monad : Monad Conv := {
    Return := fun A (x:A) (s:conv_state) => (x,s) ; 
    Bind := fun A B (c:Conv A) (f:A -> Conv B) (s:conv_state) => 
      let (v,s') := c s in f v s'
  }.
  intros ; apply Coqlib.extensionality ; auto.
  intros ; apply Coqlib.extensionality ; intros. destruct (c x). auto.
  intros ; apply Coqlib.extensionality ; intros. destruct (f x) ; auto. 
  Defined.
  Definition runConv (c:Conv unit) : (list rtl_instr) := 
    match c {|c_rev_i := nil ; c_next:=0|} with 
      | (_, c') => (List.rev (c_rev_i c'))
    end.
  Definition EMIT(i:rtl_instr) : Conv unit := 
    fun s => (tt,{|c_rev_i := i::(c_rev_i s) ; c_next := c_next s|}).
  Notation "'emit' i" := (EMIT i) (at level 75) : monad_scope.
  Definition fresh s (almost_i : pseudo_reg s -> rtl_instr) : Conv (pseudo_reg s) := 
    fun ts => let r := c_next ts in 
              let ts' := {|c_rev_i := (almost_i (ps_reg s r))::c_rev_i ts ; 
                           c_next := r + 1|} in 
                (ps_reg s r, ts').

  Definition load_Z s (i:Z) := fresh (load_imm_rtl (@Word.repr s i)).
  Definition load_int s (i:int s) := fresh (load_imm_rtl i).
  Definition arith s b (r1 r2:pseudo_reg s) := fresh (arith_rtl b r1 r2).
  Definition test s t (r1 r2:pseudo_reg s) := fresh (test_rtl t r1 r2).
  Definition cast_u s1 s2 (r:pseudo_reg s1) := fresh (@cast_u_rtl s1 s2 r).
  Definition cast_s s1 s2 (r:pseudo_reg s1) := fresh (@cast_s_rtl s1 s2 r).
  Definition read_byte (a:pseudo_reg size8) := fresh (get_byte_rtl a).
  Definition write_byte (v:pseudo_reg size8) (a:pseudo_reg size8) := 
    emit set_byte_rtl v a.
  Definition psw_addr := load_Z size_addr hD0. 
  Definition acc_addr := load_Z size_addr hE0. 
  Check read_byte.
  Check psw_addr.
  Definition reg2ps_reg (r:register)  :=
    offset <- load_int (register_to_i size_addr r);
    psw <- psw_addr;
    a <- read_byte psw;
    three <- load_Z size_addr 3;
    four <- load_Z size_addr 4;
    eight <- load_Z size_addr 8;
    s1 <- load_Z size_addr 0;
    s8 <- load_Z size_addr 7;
    v <- arith shru_op a four;
    rhi <- cast_u size1 v;
    v <- arith shru_op a three;
    rlo <- cast_u  size1 v;
    bank <- load_Z size_addr 0;
    emit if_rtl rhi (arith_rtl add_op bank eight bank);;
         emit if_rtl rlo  (arith_rtl add_op bank eight bank);;
     arith add_op offset bank.
        
  Check reg2ps_reg.
  Definition load_reg (r:register) :=
    reg <- reg2ps_reg r;
    read_byte reg.
  Check load_reg.
  Definition set_reg (p:pseudo_reg size_addr) (r:register) := 
    reg <- reg2ps_reg r;
    write_byte reg p.

  Definition get_pc := fresh (get_loc_rtl pc_loc).
  Definition set_pc v := emit set_loc_rtl v pc_loc.
  Definition not {s} (p: pseudo_reg s) : Conv (pseudo_reg s) :=
    mask <- load_Z s (Word.max_unsigned s);
    arith xor_op p mask.

  (* Copy the contents of rs to a new pseudo register *)
  Definition copy_ps s (rs:pseudo_reg s) := fresh (@cast_u_rtl s s rs).


  (* compute an effective address *)




  (*Definition load_mem32 (seg: segment_register) (addr: pseudo_reg size32) :=
    b0 <- lmem seg addr;
    one <- load_Z size32 1;
    addr1 <- arith add_op addr one;
    b1 <- lmem seg addr1;
    addr2 <- arith add_op addr1 one;
    b2 <- lmem seg addr2;
    addr3 <- arith add_op addr2 one;
    b3 <- lmem seg addr3;

    w0 <- cast_u size32 b0;
    w1 <- cast_u size32 b1;
    w2 <- cast_u size32 b2;
    w3 <- cast_u size32 b3;
    eight <- load_Z size32 8;
    r0 <- arith shl_op w3 eight;
    r1 <- arith or_op r0 w2;
    r2 <- arith shl_op r1 eight;
    r3 <- arith or_op r2 w1;
    r4 <- arith shl_op r3 eight;
    arith or_op r4 w0.*)
    


  (* given a prefix and w bit, return the size of the operand *)
  Definition opsize override w :=
    match override, w with
      | _, false => size8
      | true, _ => size16
      | _,_ => size32
    end.

  (* load the value of an operand into a pseudo register *)
  (**********************************************)
  (*   Conversion functions for instructions    *)
  (**********************************************)

  (************************)
  (* Arith ops            *)
  (************************)

  Definition read_indirect i :=
    match i with
      | ind_reg r =>
        rv <- load_reg r;
        read_byte rv

      (* | ind_dptr => *)

      (* | ind_a_dptr => *)
      (* | ind_a_pc => *)
    end.

  Local Open Scope Z_scope.
  Definition valid_bit_addr := map (@Word.repr size8) (flat_map
                                (fun x => x+8::x+7::x+6::x+5::x+4::x+3::x+2::x+1::x::nil)
                                   (hF0::hE0::hD0::hC8::hB8::hB0::
    hA8::hA0::h98::h90::h88::h80::nil)).
  Local Close Scope Z_scope.
  Definition is_valid_bit_addr baddr :=
    let prop := (fun s => Word.eq s baddr ) in
    match find  prop valid_bit_addr with
      | Some _ => true
      | Nothing => false
      end.
  Definition conv_SETB (op1:operand) : Conv unit :=
    match op1 with
        | Bit_op (bit_addr baddr) =>
          if is_valid_bit_addr baddr then
            let addr := Word.and baddr (Word.repr  3) in
            let bsel := Word.and baddr (Word.not (Word.repr 3)) in
            let ormask := Word.shl (Word.repr 1) bsel in
            ormaskReg <- load_int ormask;
            a <- load_int addr;
            av <- read_byte a;
            av' <- arith or_op av ormaskReg;
            write_byte av' a
            else
              emit error_rtl
        | _ => emit error_rtl
    end.

  Definition conv_CLR (op1:operand) : Conv unit :=
    match op1 with
        | Bit_op (bit_addr baddr) =>
          if is_valid_bit_addr baddr then
            let addr := Word.and baddr (Word.repr  3) in
            let bsel := Word.and baddr (Word.not (Word.repr 3)) in
            let andmask := Word.not (Word.shl (Word.repr 1) bsel) in
            andmaskReg <- load_int andmask;
            a <- load_int addr;
            av <- read_byte a;
            av' <- arith and_op av andmaskReg;
            write_byte av' a
            else
              emit error_rtl
        | Acc_op =>
          
          a <- acc_addr;
          b <- load_Z size8 0;
          write_byte b a
          
        | _ => emit error_rtl
    end.

  Definition conv_NOP : Conv unit := (** TODO: Better way to NOP? **)
    a <- acc_addr;
    av <- read_byte a;
    write_byte av a.
            
   Definition conv_ANL  (op1 op2: operand) : Conv unit :=
     a <- acc_addr;
     av <- read_byte a;
     match op1 with
       |  Acc_op =>
          match op2 with
          | Reg_op r =>
            rv <- load_reg r;
            av' <- arith and_op av rv;
            write_byte av' a

          | Indirect_op i =>
            rv <- read_indirect i;
            av' <- arith and_op av rv;
            write_byte av' a
          | Direct_op i =>
            addr <- load_int i;
            rv <- read_byte addr;
            av' <- arith and_op av rv;
            write_byte av' a
          | Imm_op i =>
            rv <- load_int i;
            av' <- arith and_op av rv;
            write_byte av' a
          | _ => emit error_rtl
        end
     |  Direct_op d =>
        match op2 with
          | Acc_op =>
            r <- load_int d;
            rv <- read_byte r;
            rv' <- arith and_op av rv;
            write_byte rv' r
          | Imm_op i =>
            r <- load_int d;
            iv <- load_int i;
            dv <- read_byte r;
            rv' <- arith and_op av iv;
            write_byte rv' r
          | _ => emit error_rtl
        end
     | _ => emit error_rtl
   end.
                                          
  
  (* Just a filter for some prefix stuff we're not really handling yet.
     In the future this should go away. *)


  (*
  Definition conv_REP_generic (zfval: option Z) (oldpc_val: Word.int size32) :=
    oldecx <- load_reg ECX;
    one <- load_Z _ 1;
    newecx <- arith sub_op oldecx one;
    emit set_loc_rtl newecx (reg_loc ECX);;
    zero <- load_Z _ 0;
    oldpc <- load_int oldpc_val;
    op_guard <- test eq_op newecx zero;
    guard <- not op_guard;
    emit if_rtl guard (set_loc_rtl oldpc pc_loc);;
    match zfval with
      | None => ret tt
      | Some z => v <- load_Z _ z;
                  zf <- get_flag ZF;
                  op_guard2 <- test eq_op zf v;
                  guard2 <- not op_guard2;
                  emit if_rtl guard2 (set_loc_rtl oldpc pc_loc)
    end.     

  Definition conv_REP := conv_REP_generic None.
  Definition conv_REPE := conv_REP_generic (Some 0%Z).
  Definition conv_REPNE := conv_REP_generic (Some 1%Z).

  Definition conv_lock_rep (pre: prefix) (i: instr) :=
      match lock_rep pre with 
        | Some lock | None => ret tt
        | Some rep => match i with
                        | MOVS _ => conv_REP oldpc
                        | LODS _ => conv_REP oldpc
                        | CMPS _ => conv_REPE oldpc
                        | STOS _ => conv_REP oldpc
                        | _ => emit error_rtl
                      end
        | _ => emit error_rtl
      end.
  *)

  Definition instr_to_rtl (i: instr) :=
    runConv 
    (match i with
         | ANL  op1 op2 => conv_ANL  op1 op2
         | _ => emit error_rtl 
    end
    ).

End i8051_Decode.

Local Open Scope Z_scope.
Local Open Scope monad_scope.
Import i8051_Decode.
Import i8051_RTL.
Import i8051_MACHINE.


(** Go into a loop trying to parse an instruction.  We iterate at most [n] times,
    and at least once.  This returns the first successful match of the parser
    as well as the length (in bytes) of the matched instruction.  Right now, 
    [n] is set to 15 but it should probably be calculated as the longest possible
    match for the instruction parsers.  The advantage of this routine over the
    previous one is two-fold -- first, we are guaranteed that the parser only
    succeeds when we pass in bytes.  Second, we only fetch bytes that are
    needed, so we don't have to worry about running out side a segment just
    to support parsing.
*)
Fixpoint parse_instr_aux
  (n:nat) (loc:int size_pc) (len:positive) (ps:Decode.i8051_PARSER.instParserState) : 
  RTL (instr * positive) := 
  match n with 
    | 0%nat => Fail _ 
    | S m => b <- get_code_byte loc ; 
             match Decode.i8051_PARSER.parse_byte ps b with 
               | (ps', nil) => 
                 parse_instr_aux m (Word.add loc (Word.repr 1)) (len + 1) ps'
               | (_, v::_) => ret (v,len)
             end
  end.

Definition parse_instr (pc:int size_pc) : RTL ( instr * positive) :=

  pc <- get_loc pc_loc ; 
  (* add the PC to it *)
    parse_instr_aux 15 pc 1 Decode.i8051_PARSER.initial_parser_state.

(** Fetch an instruction at the location given by the program counter.  Return
    the abstract syntax for the instruction, along with a count in bytes for 
    how big the instruction is.  We fail if the bits do not parse, or have more
    than one parse.  We should fail if these locations aren't mapped, but we'll
    deal with that later. *)
Definition fetch_instruction (pc:int size_pc) : RTL ( instr * positive) :=
  [pi, len] <- parse_instr pc;
  ret (pi,len).

Fixpoint RTL_step_list l :=
  match l with
    | nil => ret tt
    | i::l' => interp_rtl i;; RTL_step_list l'
  end.

Definition run_rep 
   (ins: instr) (default_new_pc : int size_pc) : RTL unit := 
  RTL_step_list (i8051_Decode.instr_to_rtl ins);;
ret tt.

Definition step : RTL unit := 
  flush_env;;
  pc <- get_loc pc_loc ; 
  (* check if pc is in the code region; 
     different from the range checks in fetch_instruction; 
     this check makes sure the machine safely fails when pc is 
     out of bounds so that there is no need to fetch an instruction *)
    [instr,length] <- fetch_instruction pc ; 
    let default_new_pc := Word.add pc (Word.repr (Zpos length)) in
          run_rep  instr default_new_pc.

Definition step_immed (m1 m2: rtl_state) : Prop := step m1 = (Okay_ans tt, m2).
Notation "m1 ==> m2" := (step_immed m1 m2) (at level 55, m2 at next level).
Require Import Relation_Operators.
Definition steps := clos_refl_trans rtl_state step_immed.
Notation "m1 '==>*' m2" := (steps m1 m2) (at level 55, m2 at next level).


