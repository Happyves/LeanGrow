
import LeanGrow.F.Data.RExprTests.RExpr

#check 1


def RExpr.getApp (ce : RExpr): RExpr × List RExpr :=
  let rec go (args : List RExpr) : RExpr → RExpr × List RExpr
    | .app h a => go (a :: args) h
    | h => (h, args.reverse)
  go [] ce



-- def RExpr.mkApp (n : Name) (lvl : List Level) (args : List RExpr) : RExpr :=
--   sorry
