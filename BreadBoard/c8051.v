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
  Definition computeitString cycle init := 
    match ihx_to_byte_assoc_line (asciis init) None (Some nil) with
      | Some bytes => computeit cycle  (load_code_bytes bytes)
      | None => computeit cycle (load_code_bytes nil)
      end.

End c8051.


Extraction Language Ocaml.
Extraction "extract/test.ml" c8051.  