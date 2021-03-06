
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
Require Import Vector.
Import Vector.
Module Type IO_SIG.
  Variable t : Type.
  Variable trace : nat -> Type.  (* forall n, Vector.t Set n . *)
  Variable func :  Type.
  (* Variable nargs : func -> nat. *)
End IO_SIG.

Module IO.
  Definition t :=  nat.
  Definition trace := fun c => Vector.t t c.
  Definition traces :=  fun n c => Vector.t (trace c) n .
  Definition func :=fun  n => (forall {c},  (Vector.t (IO.trace c ) n  -> t)).
  Check func.
  (* Definition nargs (f:forall n, IO.func n) := match f with *)
  (*                                                 | IO.func n=> n *)
  (*                                                 end. *)
                          End IO.

Check (IO.func 10).
Definition f   : (IO.func 10  ) := fun c => fun x =>(10).

(* Definition NilTrace : IO.trace 0 := Vector.nil. *)
