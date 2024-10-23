
import LeanGrow.F.Data.RExprTests.RExpr
import LeanGrow.F.Data.CExpr.Types
import Lean.Structure



#exit

def CExpr.toRExpr : CExpr → RExpr
| .failed => .failed "Failure in CExpr"
| .lnode i _ t => .lnode i t
| .gnode i _ => .gnode i
| .lit l => .lit l
| .sort l => .sort l
| .bvar i => .bvar i
