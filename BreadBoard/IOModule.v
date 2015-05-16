
Module Type IO_SIG.
  Variable t : Type.
  Variable trace : Set.
  Variable func : Set.
  Variable nargs : func -> nat.
End IO_SIG.

Module IO.
  Definition t :=  nat.
  Definition trace := list (list t).
  Inductive func_ :=
  | fn_args : nat -> (trace -> t) -> func_.
  Definition func := func_.
  Definition nargs f :=
    match f with
      | fn_args n _ => n
    end.
End IO.