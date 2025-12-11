
@[extern "extern_export_trick"]
opaque eeTrick : Nat → Nat

@[extern "fun_one"]
opaque funOne : UInt32 → UInt32

@[export extern_export_trick]
partial def eeTrickImp (n : Nat) : Nat :=
  if n == 0
  then 1
  else n * (eeTrick (n-1))
