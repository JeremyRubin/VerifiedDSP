
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
  Definition trace := forall n, Vector.t t n.
  Definition traces :=  fun n => Vector.t (Vector.t t n) .
  Definition func : nat->Type := fun n => (Vector.t (list IO.t ) n  -> t).
  Check func.
  (* Definition nargs (f:forall n, IO.func n) := match f with *)
  (*                                                 | IO.func n=> n *)
  (*                                                 end. *)
                          End IO.
Definition f  : (IO.func 10) := fun x =>(10).
Definition NilTrace : IO.trace := Vector.const 0.
