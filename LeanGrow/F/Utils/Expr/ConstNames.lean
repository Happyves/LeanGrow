
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


partial def Expr.getConstNamesF (e : Expr) : List Name :=
  let rec go (done : List Name) : List Expr → List Name
  | [] => []
  | x :: L =>
      match x with
      | .const n _ => go (n :: done) L
      | .app l r => go done (l :: r :: L)
      | .lam _ l r _ => go done (l :: r :: L)
      | .forallE _ l r _ => go done (l :: r :: L)
      | .letE _ t l r _ => go done (t :: l :: r :: L)
      | .proj n _ e => go (n :: done) (e :: L)
      | .mdata _ e => go done (e :: L)
      | _ => []
  go [] [e]
