
import LeanGrow.F.Data.CExpr.ReduceInferSmart.Whnf
import LeanGrow.F.Data.CExpr.ReduceInferSmart.Infer

open Lean


mutual

partial def cexprInferType (fctx : FixCtx) (bvarCtx : List CExpr) (e : CExpr) :=
  cexprInferTypeImp fctx bvarCtx e cexprInferType cexprWhnf

partial def cexprWhnf (fctx : FixCtx) (bvarCtx : List CExpr) (e : CExpr) :=
  cexprWhnfImp fctx bvarCtx e cexprInferType cexprWhnf

end
