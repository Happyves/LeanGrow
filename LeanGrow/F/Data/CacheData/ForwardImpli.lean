
import LeanGrow.F.Data.CExpr.Types
import LeanGrow.F.Utils.Expr.GetHyps


namespace CacheType

structure Fwd where
  cst_name : Name
  cst_level_params : List Name
  thm_data : Array EmbedData
  thm_order : Array Nat


#check Lean.Expr.getHypsGoal
