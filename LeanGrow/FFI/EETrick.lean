

import LeanGrow.FFI.Lffi


@[export extern_export_trick]
partial def eeTrickImp (n : Nat) : Nat :=
  if n == 0
  then 1
  else n * (eeTrick (n-1))
