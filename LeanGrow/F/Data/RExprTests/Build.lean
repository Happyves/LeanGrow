
import LeanGrow.F.Data.RExprTests.Eta


#check 1

/-
TODO
- build struc, recu, mat from applications
- determin prop-typed terms, and wrap them in .proof
-/



#exit

def CExpr.toRExpr : CExpr → RExpr
| .failed => .failed "Failure in CExpr"
| .lnode i _ t => .lnode i t
| .gnode i _ => .gnode i
| .lit l => .lit l
| .sort l => .sort l
| .bvar i => .bvar i
