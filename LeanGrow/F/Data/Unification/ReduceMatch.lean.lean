
import LeanGrow.F.Data.CExpr.Types


#check 1

inductive NodeExpr where
| ofNode (i : Nat)
| ofCExpr (c : CExpr)
deriving Inhabited, Repr, BEq



def CExpr.ReduceMatchAssign (l r : CExpr) : Option (List (Nat × NodeExpr)) :=
  sorry
