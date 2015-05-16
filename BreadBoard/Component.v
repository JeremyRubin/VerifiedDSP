
Import IO.
Module Type Component_Sig(IO:IO_SIG).
  Variable io : IO.func.
End Component_Sig.

Module Component(I:IO_SIG)(M:Component_Sig(I)).
  Import M.
  Definition io := M.io.
End Component.
