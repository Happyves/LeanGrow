
import Lean.Expr

open Lean

-- fix wrt ↓ CExpr.getConstNames
def Expr.getConstNames : Expr → List Name
| .const n _ => [n]
| .app l r => (Expr.getConstNames l) ++ (Expr.getConstNames r)
| .lam _ l r _ => (Expr.getConstNames l) ++ (Expr.getConstNames r)
| .forallE _ l r _ => (Expr.getConstNames l) ++ (Expr.getConstNames r)
| .letE _ t l r _ => (Expr.getConstNames t) ++(Expr.getConstNames l) ++ (Expr.getConstNames r)
| .mdata _ e => (Expr.getConstNames e)
| .proj n _ e => n :: (Expr.getConstNames e)
| _ => []
