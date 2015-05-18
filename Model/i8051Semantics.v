
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

  Inductive loc : nat -> Set := 
  | pc_loc : loc size_pc
  | P0_loc : loc size8
  | P1_loc : loc size8
  | P2_loc : loc size8
  | P3_loc : loc size8
  | pc_mod_loc : loc size1.


  Definition location := loc.

  Definition fmap (A B:Type) := A -> B.
  Definition upd A (eq_dec:forall (x y:A),{x=y}+{x<>y}) B (f:fmap A B) (x:A) (v:B) : 
    fmap A B := fun y => if eq_dec x y then v else f y.
  Definition look A B (f:fmap A B) (x:A) : B := f x.
  Record ports := {P0 : int size8;
                   P1 : int size8;
                   P2 : int size8;
                   P3 : int size8}.
  Record mach := { 
    pc_reg : int size_pc;
    external : ports;
    pc_mod : int size1
  }.
  Definition mach_state := mach.

  Definition get_location s (l:loc s) (m:mach_state) : int s := 
    match l in loc s' return int s' with 
      | pc_loc => pc_reg m
      | P0_loc => P0 (external m)
      | P1_loc => P1 (external m)
      | P2_loc => P2 (external m)
      | P3_loc => P3 (external m)
      | pc_mod_loc => pc_mod m
    end.



  Definition set_pc v m  :=  {|
       pc_reg := v;
       pc_mod := pc_mod m;
       external := external m
    |}.
  Definition set_pc_mod v m  :=  {|
       pc_reg :=pc_reg m;
       pc_mod := v;
       external := external m
    |}.
  Definition set_external f m:= {|
                                 pc_reg := pc_reg m;
                                 pc_mod := pc_mod m;
                                 external := f
                                               |}.
                                
  Definition set_location s (l:loc s) (v:int s) (m:mach_state) := 
    match l in loc s' return int s' -> mach_state with 
      | pc_loc => fun v => set_pc v m
      | pc_mod_loc => fun v => set_pc_mod v m
      | _ => fun _ => m (** Do Nothing **)
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
  Definition set_pc_mod v := emit set_loc_rtl v pc_mod_loc.
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
  Definition valid_bit_addr :=
    let aligned_bit_addrs := hF0::hE0::hD0::hC8::hB8::hB0::hA8::hA0::h98::h90::h88::h80::nil in
    let mk_unaligned_bit_addrs := (fun x => x+8::x+7::x+6::x+5::x+4::x+3::x+2::x+1::x::nil) in
    map (@Word.repr size8) (flat_map mk_unaligned_bit_addrs aligned_bit_addrs).
  Local Close Scope Z_scope.
  Definition is_valid_bit_addr baddr :=
    let prop := (fun s => Word.eq s baddr ) in
     existsb prop valid_bit_addr.
  Definition conv_SETB (op1:operand) : Conv unit :=
    match op1 with
        | Bit_op (bit_addr baddr) =>
          if is_valid_bit_addr baddr then
            let bsel := Word.and baddr (Word.repr  3) in
            let addr := Word.and baddr (Word.not (Word.repr 3)) in
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
            let bsel := Word.and baddr (Word.repr  3) in
            let addr := Word.and baddr (Word.not (Word.repr 3)) in
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
  Definition conv_LJMP (op : operand) : Conv unit :=
    match op with
      | Imm16_op x =>
        y <- load_int x;
        set_pc y;;
        r <- load_int (Word.repr 1);
        set_pc_mod r
      | _ => emit error_rtl
    end.
  Definition conv_JMP : Conv unit :=

    r <- load_int (Word.repr 1);
    set_pc_mod r;; 
    Pdpl <- load_Z size8 Alias.DPL;
    Pdph <- load_Z size8 Alias.DPH;
    dph <- read_byte Pdph;
    dpl <- read_byte Pdpl;
    pc <- get_pc;
    edpl <- cast_u size_pc dpl;
    edph <- cast_u size_pc dph;
    eight <- load_Z size_pc 8;
    edphS <- arith shl_op edph eight;
    dptr <- arith and_op edphS edpl;
    newPC <- arith add_op dptr pc;
    set_pc newPC.
    
            
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
  let p := {|P0 := Word.one;
            P1 := Word.one;
            P2 := Word.one;
            P3 := Word.one|} in
    runConv 
      (
        match i with
         | ANL  op1 op2 => conv_ANL  op1 op2
         (* | ADD op1 op2 => conv_ADD op1 op2 *)
         | SETB op => conv_SETB op
         | CLR op => conv_CLR op
         | LJMP op => conv_LJMP op
         | JMP => conv_JMP
         | NOP => conv_NOP
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

  (* add the PC to it *)
    parse_instr_aux 15 pc 1 Decode.i8051_PARSER.initial_parser_state.

(** Fetch an instruction at the location given by the program counter.  Return
    the abstract syntax for the instruction, along with a count in bytes for 
    how big the instruction is.  We fail if the bits do not parse, or have more
    than one parse.  We should fail if these locations aren't mapped, but we'll
    deal with that later. *)
Fixpoint fetch_n (n:nat) (loc:int size_addr) (r:rtl_state) : list int8 :=
  match n with
    | 0%nat => nil
    | S m =>
      AddrMap.get loc (rtl_memory r) ::
                  fetch_n m (Word.add loc (Word.repr 1)) r
  end.

Definition fetch_instruction (pc:int size_pc) : RTL ( instr * positive) :=
  parse_instr pc.

Fixpoint RTL_step_list l :=
  match l with
    | nil => ret tt
    | i::l' => interp_rtl i;; RTL_step_list l'
  end.

Definition run_rep 
   (ins: instr) (default_new_pc : int size_pc) : RTL unit := 
  RTL_step_list (i8051_Decode.instr_to_rtl ins);;
  z <- get_loc pc_mod_loc;
  if Word.eq Word.zero  z then (* Change pc to default if inst didn't modify it *)
    set_loc pc_loc default_new_pc
  else
    set_loc pc_mod_loc Word.zero.


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
Check set_byte.
Check get_byte.
Fixpoint nsteps ps (l:loc size8) : RTL (ports):=
  match ps with
    | nil =>
      d <- get_byte (Word.repr Alias.P3);
      b <- get_byte (Word.repr Alias.P2);
      c <- get_byte (Word.repr Alias.P1);
      a <- get_byte (Word.repr Alias.P0);
      ret {|P0:=a;P1:=b;P2:=c;P3:=d|}
    | p::r=>
      set_loc P0_loc (P0 p);;
      set_loc P1_loc (P1 p);;
      set_loc P2_loc (P2 p);;
      set_loc P3_loc (P3 p);;
      step;; nsteps r l
  end.
Definition nsteps_init (init: RTL unit) fuel (l:loc size8) : RTL (ports) :=
  init;;
  nsteps fuel l.
Definition dump_state s (ps: list ports) (init: RTL unit) : option (ports) :=
      match nsteps_init init (rev ps)  P3_loc s with
        | (Okay_ans v, rs') => Some v
        | (Fail_ans, rs') => None
        | (SafeFail_ans, rs') => None
      end.
           
Definition step_immed (m1 m2: rtl_state) : Prop := step m1 = (Okay_ans tt, m2).
Notation "m1 ==> m2" := (step_immed m1 m2) (at level 55, m2 at next level).
Require Import Relation_Operators.
Print clos_refl_trans.
Definition steps := clos_refl_trans rtl_state step_immed.
Check steps.
Notation "m1 '==>*' m2" := (steps m1 m2) (at level 55, m2 at next level).


Notation "a $ b" := (a b) (at level 90, right associativity).
(* ($) :: (a -> b) -> a -> b *)
(*                           f $ x = f x *)

Definition x := map (fun _ => step) $ (1::2::nil).
Definition lr0 : RTL (instr * positive) := ret (LJMP (Imm16_op (Word.repr (16*16))), ZIndexed.index 8).
Check map.
(* Lemma t : nstep 2 nil = lr1 -> nstep 4 nil = lr2. *)
(* Proof. *)
(*   intros. *)
(*   unfold nstep in H. *)
Fixpoint compute_parity_aux {s} op1 (op2 : pseudo_reg size1) (n: nat) :
  Conv (pseudo_reg size1) :=
  match n with
    | O => @load_Z size1 0
    | S m =>
      op2 <- compute_parity_aux op1 op2 m;
        one <- load_Z s 1;
        op1 <- arith shru_op op1 one;
        r <- cast_u size1 op1;
        @arith size1 xor_op r op2
  end.

Definition compute_parity {s} op : Conv (pseudo_reg size1) :=
  r1 <- load_Z size1 0;
  one <- load_Z size1 1;
  p <- @compute_parity_aux s op r1 8; (* ACHTUNG *)
  arith xor_op p one.
Definition lmem  (a:pseudo_reg size8) : Conv (pseudo_reg size8):=
  read_byte a.


Program Fixpoint load_mem_n  (addr:pseudo_reg size8)
        (nbytes_minus_one:nat) : Conv (pseudo_reg ((nbytes_minus_one+1) * 8 -1)%nat) :=
  match nbytes_minus_one with
    | O => lmem addr
    | S n =>
      rec <- load_mem_n addr n ;
        count <- load_Z size8 (Z_of_nat (S n)) ;
        p3 <- arith add_op addr count ;
        nb <- lmem p3 ;
        p5 <- cast_u ((nbytes_minus_one + 1)*8-1)%nat rec ;
        p6 <- cast_u ((nbytes_minus_one + 1)*8-1)%nat nb ;
        p7 <- load_Z _ (Z_of_nat (S n) * 8) ;
        p8 <- arith shl_op p6 p7 ;
        arith or_op p5 p8
  end.
Definition load_mem8  (addr:pseudo_reg size8) :=
  load_mem_n addr 0.

Definition iload_op8  (op:operand) : Conv (pseudo_reg size8) :=
  match op with
    | Imm_op i => load_int i
    | Reg_op r => load_reg r
    | Address_op a =>
      p1 <- load_int (addrDisp a) ; read_byte p1
    | Offset_op off => p1 <- load_int off;
        load_mem8 p1
    | Acc_op => acc_addr
    | Direct_op d =>  load_int d
    | Imm16_op i => acc_addr
    | Indirect_op a => match a with
                           | ind_reg i =>
                             a <- load_reg i;
                               read_byte a
                       end
    | Bit_op ( bit_addr baddr )=> 
          if is_valid_bit_addr baddr then
            let addr := Word.and baddr (Word.repr  3) in
            let bsel := Word.and baddr (Word.not (Word.repr 3)) in
            let andmask := Word.shl (Word.repr 1) bsel in
            andmaskReg <- load_int andmask;
            a <- load_int addr;
            av <- read_byte a;
            av' <- arith and_op av andmaskReg;
            bselreg <- load_int bsel;
            arith shru_op av' bselreg
            else
              acc_addr
  end. (** THIS SUCKS **)

Definition smem  (v:pseudo_reg size8) (a:pseudo_reg size8): 
  Conv unit :=
  
  write_byte v a.

Program Fixpoint set_mem_n {t} 
        (v: pseudo_reg (8*(t+1)-1)%nat) (addr : pseudo_reg size8) : Conv unit :=
  match t with
    | O => smem v addr
    | S u =>
      p1 <- cast_u (8*(u+1)-1)%nat v ;
        set_mem_n p1 addr ;;
                  p2 <- load_Z (8*(t+1)-1)%nat (Z_of_nat  ((S u) * 8)) ;
        p3 <- arith shru_op v p2 ;
        p4 <- cast_u size8 p3 ;
        p5 <- load_Z size8 (Z_of_nat (S u)) ;
        p6 <- arith add_op p5 addr ;
        smem p4 p6
  end.

Open Local Scope char_scope.
Definition nibble_ns x : option (string*nat):=
  match x with
      | "0" => Some ("0000"%string, 0%nat)
      | "1" => Some ("0001"%string, 1%nat)
      | "2" => Some ("0010"%string, 2%nat)
      | "3" => Some ("0011"%string, 3%nat)
      | "4" => Some ("0100"%string, 4%nat)
      | "5" => Some ("0101"%string, 5%nat)
      | "6" => Some ("0110"%string, 6%nat)
      | "7" => Some ("0111"%string, 7%nat)
      | "8" => Some ("1000"%string, 8%nat)
      | "9" => Some ("1001"%string, 9%nat)
      | "A" => Some ("1010"%string, 10%nat)
      | "B" => Some ("1011"%string, 11%nat)
      | "C" => Some ("1100"%string, 12%nat)
      | "D" => Some ("1101"%string, 13%nat)
      | "E" => Some ("1110"%string, 14%nat)
      | "F" => Some ("1111"%string, 15%nat)
      | _ => None
  end.
  
Definition nibble x : option nat:=
  match nibble_ns x with
      | Some (_,n) => Some n
      | _ => None
  end.

Open Local Scope nat_scope.
Definition maybe_app {A:Type} a (m: option (list A)) := match m with | Some v =>  Some (a::v) | None => None end.
(* Intel hex is weird *)
 (* Fixpoint ihx_to_byte_assoc_line ihx (linestate:option (nat*nat)) acc:= *)
 (*  match linestate, ihx with *)
 (*      (** `byte` == `nibble`* `nibble`**) *)
 (*    (** `:` (length data :`byte`) (address: `byte` * `byte`) (type : `byte`)  (data :list `byte`) **) *)
 (*    | None, ":"::fuel1::fuel2 *)
 (*         ::high_addr1::high_addr2 *)
 (*         ::low_addr1::low_addr2 *)
 (*         ::control1::control2::r => *)
 (*      match control1, control2 with *)
 (*        |"0", "1" => acc *)
 (*        |"0", "0" => *)
 (*         match nibble fuel1, nibble fuel2 *)
 (*               , nibble high_addr1, nibble high_addr2 *)
 (*               , nibble low_addr1, nibble low_addr2 *)
 (*         with *)
 (*           | Some a, Some b, Some c, Some d, Some e, Some f => *)
 (*             let addr := ((c*16+d)*16 + e)*16 + f in *)
 (*             let fuel := a*16+b in  *)
 (*             ihx_to_byte_assoc_line r (Some (fuel, addr)) acc *)
 (*           | _, _, _, _, _, _ => *)
 (*             None *)
 (*         end *)
 (*        |_, _ => ihx_to_byte_assoc_line r None acc *)
 (*      end *)
 (*    (** Extract a bytes **) *)
 (*    | Some (fuel, addr), a::b::r => *)
 (*      match fuel, nibble a, nibble b with *)
 (*        | O, checksum1, checksum2 => *)
 (*          (* let checksum := checksum1*16 + checksum2 in *) *)
 (*          ihx_to_byte_assoc_line r None acc *)
 (*        | S n, Some hi, Some lo => *)
 (*          ihx_to_byte_assoc_line r (Some (n, addr+1)) (maybe_app (addr, (hi*16)+lo) acc) *)
 (*        | _, _, _ => None *)
 (*      end *)
 (*    | _, _ => acc *)
                
 (*    end. *)

 Require Import Ascii.
 Fixpoint asciis (s:string) : list ascii:=
   match s with
       | EmptyString => nil
       | String c r => c:: asciis r
                        end.

 Definition to_ascii := map asciis.

 Definition line_to_program x := fold_right (fun s x =>  app (s++"010"::nil) x ) nil x.
 Fixpoint  load_code_bytes (b: list (nat * nat)) : RTL unit :=
   match b with
     |(addr, code)::r =>
      set_code_byte (Word.repr (Z_of_nat addr)) (Word.repr (Z_of_nat code));;
        load_code_bytes r
     |_ =>ret tt
   end.
   
 Fixpoint  load_code_bytes_bin (b: list nat) (start:nat) : RTL unit :=
   match b with
     |code::r =>
      set_code_byte (Word.repr (Z_of_nat start)) (Word.repr (Z_of_nat code));;
        load_code_bytes_bin r (S start)
     |_ =>ret tt
   end.

 