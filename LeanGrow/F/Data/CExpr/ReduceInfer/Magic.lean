
import LeanGrow.F.Data.CExpr.Types

@[extern 6 "lean_my_whnf"] opaque cexprWhnf : CExpr → CExpr
@[extern 6 "lean_my_infer_type"] opaque cexprInferType (bvarCtx : List CExpr) : CExpr → CExpr
