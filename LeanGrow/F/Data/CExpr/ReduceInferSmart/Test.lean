
import LeanGrow.F.Data.CExpr.ReduceInferSmart.Top

#check 1

def FunImp (n : Nat) (f : Nat → Nat) : Nat :=
  if n = 1
  then n
    else
      if n%2 = 0
      then f (n/2)
      else f (3*n+1)



partial def Fun (n : Nat) := FunImp n Fun

#eval Fun 4
