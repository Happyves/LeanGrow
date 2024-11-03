
import LeanGrow.F.Data.CExpr.Types
import LeanGrow.F.Utils.Trie.CTrie
import LeanGrow.F.Data.CExpr.ReduceInfer.ConstInfo

#check 1

structure FixCtx where
  gnodeTypes : List (Array CExpr)
  gnodeTypesHandler : Nat → (Nat × Nat)
  ltxTypes : List (Nat × Array EmbedData)
  current : Option (Array EmbedData)
  cstData : CTrie CstInfo
  deriving Inhabited


@[extern 6 "lean_my_whnf"] opaque cexprWhnf
  (fctx : FixCtx) (bvarCtx : List CExpr) : CExpr → CExpr


@[extern 6 "lean_my_infer_type"] opaque cexprInferType
  (fctx : FixCtx) (bvarCtx : List CExpr) : CExpr → CExpr
