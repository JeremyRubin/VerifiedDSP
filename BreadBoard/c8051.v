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
Definition default := {| executing := NOP;
                         pc := Word.repr 0;
                         cycle := 0;
                         output := {| P0:=Word.repr 0;P1:=Word.repr 0;P2:=Word.repr 0;P3:=Word.repr 0 |}
                      |}.
Definition m_init   :=  {|
                        pc_reg := Word.repr  0;
                        trace := [];
                        external := (fun tr => let t := hd  default tr in 
                                              {| executing := executing t;
                                                 pc := pc t;
                                                 cycle := cycle t;
                                                 output := {| P0:=Word.repr 0;P1:=Word.repr 0;P2:=Word.repr 0;P3:=Word.repr 0 |}

                                              |})
                      |}.
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
  
Module c8051.
  (* Variable threshold : nat. *)
  Definition threshold := 1.
  Search nat.
  Definition digitizer : IO.func :=
    IO.fn_args 1 (fun x =>
                    match threshold - (hd 0 (hd [] x)) with
                      | 0 => 1
                      | _ => 0
                    end).
  Fixpoint digitize l acc :=
    match l with
      | (a, b) :: r => digitize r (acc // a ~> digitizer  ~> b # b ("Digitized Port"))
      | [] => acc
    end.

  (* Definition mk8051 (code:string) (pinmap:list (nat * nat)) := *)

  

  Definition computeit cycle init := dump_state cycle {|
    rtl_oracle :=  {|
    oracle_bits := Word.repr ; 
    oracle_offset := 0
  |}; 
    rtl_env := empty_env ; 
    rtl_mach_state := m_init; 
    rtl_memory := AddrMap.init (Word.repr 0);
    rtl_code := CodeMap.init (Word.repr 0)
  |} init.

  Definition t := (computeit 1).
End c8051.

Require Import Ascii.
 Definition prg_line : list (list ascii):=
   (map asciis (":03000000020006F5"%string::
":03005F0002000399"%string::
":0300030002006296"%string::
":07006200C300D3020062227B"%string::
":06003500E478FFF6D8FD9F"%string::
":200013007900E94400601B7A0090006D780075A000E493F2A308B8000205A0D9F4DAF27527"%string::
":02003300A0FF2C"%string::
":20003B007800E84400600A790075A000E4F309D8FC7800E84400600C7900900000E4F0A3C5"%string::
":04005B00D8FCD9FAFA"%string::
":0D000600758107120069E5826003020003A6"%string::
":04006900758200227A"%string::
":00000001FF"%string::nil)).
Definition bytes := (ihx_to_byte_assoc_line (line_to_program prg_line)
              None (Some nil)).

 Definition mainFN (t:unit) :=
   match bytes with
       | Some bytes => c8051.computeit 10 (load_code_bytes bytes)
       | None => None
                   end.
Extraction Language Ocaml.
Extraction "extract/test.ml" mainFN.  