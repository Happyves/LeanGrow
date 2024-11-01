
import LeanGrow.F.Data.CExpr.Types
import LeanGrow.F.Utils.Trie.CTrie
import LeanGrow.F.Data.CExpr.ReduceInfer.ConstInfo

@[extern 6 "lean_my_whnf"] opaque cexprWhnf
  (gnodeTypes : List (Array CExpr)) (gnodeTypesHandler : Nat → (Nat × Nat))
  (ltxTypes : List (Array EmbedData)) (current : Option (Array EmbedData))
  (cstData : CTrie CstInfo) (bvarCtx : List CExpr) : CExpr → CExpr


@[extern 6 "lean_my_infer_type"] opaque cexprInferType
  (gnodeTypes : List (Array CExpr)) (gnodeTypesHandler : Nat → (Nat × Nat))
  (ltxTypes : List (Array EmbedData)) (current : Option (Array EmbedData))
  (cstData : CTrie CstInfo) (bvarCtx : List CExpr) : CExpr → CExpr
