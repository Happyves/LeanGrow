
import LeanGrow.F.Data.CExpr.Types

open Lean

def Lean.Expr.toCExpr : Expr → CExpr
| .bvar i => .bvar i
| .fvar _ => .failed
| .mvar _ => .failed
| .sort l => .sort l
| .const n ll => .const n ll
| .app f a => .app (Expr.toCExpr f) (Expr.toCExpr a)
| .lam n t b i => .lam n (Expr.toCExpr t) (Expr.toCExpr b) i
| .forallE n t b i => .forallE n (Expr.toCExpr t) (Expr.toCExpr b) i
| .letE n t v b i => .letE n (Expr.toCExpr t) (Expr.toCExpr v) (Expr.toCExpr b) i
| .lit l => .lit l
| .proj t i b => .proj t i (Expr.toCExpr b)
| .mdata _ e => (Expr.toCExpr e)


def CExpr.hasNodes : CExpr → Bool
| .node _ _ => true
| .app f a => (CExpr.hasNodes f) || (CExpr.hasNodes a)
| .lam _ t b _ => (CExpr.hasNodes t) || (CExpr.hasNodes b)
| .forallE _ t b _ => (CExpr.hasNodes t) || (CExpr.hasNodes b)
| .letE _ t v b _ => (CExpr.hasNodes t) || (CExpr.hasNodes b) || (CExpr.hasNodes v)
| .proj _ _ b => (CExpr.hasNodes b)
| _ => false


def CExpr.toExpr : CExpr → Option Expr
| .node _ _ => .none
| .bvar i => .some (.bvar i)
| .sort l => .some (.sort l)
| .const n ll => .some (.const n ll)
| .app f a =>
      match CExpr.toExpr f, CExpr.toExpr a with
      | .some f', .some a' => .some (.app f' a')
      | _ , _ => .none
| .lam n t b B =>
      match CExpr.toExpr t, CExpr.toExpr b with
      | .some t', .some b' => .some (.lam n t' b' B)
      | _ , _ => .none
| .forallE n t b B =>
      match CExpr.toExpr t, CExpr.toExpr b with
      | .some t', .some b' => .some (.forallE n t' b' B)
      | _ , _ => .none
| .letE n t v b B =>
      match CExpr.toExpr t, CExpr.toExpr v, CExpr.toExpr b with
      | .some t', .some v', .some b' => .some (.letE n t' v' b' B)
      | _ , _, _ => .none
| .lit l => .some (.lit l)
| .proj t i b => (.proj t i) <$> (CExpr.toExpr b)
| .failed => .none



def CExpr.getConstNames : CExpr → List Name
| .const n _ => [n]
| .app l r => (CExpr.getConstNames l) ++ (CExpr.getConstNames r)
| .lam _ l r _ => (CExpr.getConstNames l) ++ (CExpr.getConstNames r)
| .forallE _ l r _ =>  ((CExpr.getConstNames l) ++ (CExpr.getConstNames r))
| .letE _ t l r _ => (CExpr.getConstNames t) ++(CExpr.getConstNames l) ++ (CExpr.getConstNames r)
| .proj n _ e => n :: (CExpr.getConstNames e)
| .sort _ => []
| _ => []

partial def CExpr.getConstNamesF (e : CExpr) : List Name :=
  let rec go : List CExpr → List Name
  | [] => []
  | x :: L =>
      match x with
      | .const n _ => n :: (go L)
      | .app l r => go (l :: r :: L)
      | .lam _ l r _ => go (l :: r :: L)
      | .forallE _ l r _ => go (l :: r :: L)
      | .letE _ t l r _ => go (t :: l :: r :: L)
      | .proj n _ e => n :: (go [e])
      | _ => []
  go [e]
