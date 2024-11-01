
import LeanGrow.F.Data.CExpr.ReduceInfer.BetaZeta
import LeanGrow.F.Data.CExpr.ReduceInfer.Nabla
import LeanGrow.F.Data.CExpr.ReduceInfer.Delta
import LeanGrow.F.Data.CExpr.ReduceInfer.Iota
import LeanGrow.F.Data.CExpr.ReduceInfer.Magic

open Lean





#exit

@[export lean_my_whnf]
def cexprWhnfImp
  (gnodeTypes : List (Array CExpr)) (gnodeTypesHandler : Nat → (Nat × Nat))
  (ltxTypes : List (Array EmbedData)) (current : Option (Array EmbedData))
  (cstData : CTrie CstInfo) (bvarCtx : List CExpr) (ce : CExpr) : CExpr := sorry
