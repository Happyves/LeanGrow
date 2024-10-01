
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


partial def Lean.Expr.toCExprF (E : Expr) : CExpr :=
  let rec go : List Expr → List CExpr
      | [] => []
      | nx :: L =>
            match nx with
            | .bvar i => .bvar i :: (go L)
            | .fvar _ => .failed :: (go L)
            | .mvar _ => .failed :: (go L)
            | .sort l => .sort l :: (go L)
            | .const n ll => .const n ll :: (go L)
            | .app f a =>
                  let r := go (f :: a :: L)
                  let F := List.headD r .failed
                  let A := List.headD (List.drop 1 r) .failed
                  (.app F A) :: (List.drop 2 r)
            | .lam n t b i =>
                  let r := go (t :: b :: L)
                  let T := List.headD r .failed
                  let B := List.headD (List.drop 1 r) .failed
                  (.lam n T B i) :: (List.drop 2 r)
            | .forallE n t b i =>
                  let r := go (t :: b :: L)
                  let T := List.headD r .failed
                  let B := List.headD (List.drop 1 r) .failed
                  (.forallE n T B i) :: (List.drop 2 r)
            | .letE n t v b i =>
                  let r := go (t :: v :: b :: L)
                  let T := List.headD r .failed
                  let V := List.headD (List.drop 1 r) .failed
                  let B := List.headD (List.drop 2 r) .failed
                  (.letE n T V B i) :: (List.drop 3 r)
            | .lit l => .lit l :: (go L)
            | .proj t i b =>
                  let r := go (b :: L)
                  let B := List.headD r .failed
                  (.proj t i B) :: (List.drop 1 r)
            | .mdata _ e => go (e :: L)
  List.headD (go [E]) .failed




def CExpr.hasNodes : CExpr → Bool
| .node _ _ => true
| .app f a => (CExpr.hasNodes f) || (CExpr.hasNodes a)
| .lam _ t b _ => (CExpr.hasNodes t) || (CExpr.hasNodes b)
| .forallE _ t b _ => (CExpr.hasNodes t) || (CExpr.hasNodes b)
| .letE _ t v b _ => (CExpr.hasNodes t) || (CExpr.hasNodes b) || (CExpr.hasNodes v)
| .proj _ _ b => (CExpr.hasNodes b)
| _ => false


partial def CExpr.hasNodesF (E : CExpr) : Bool :=
      let rec go : List CExpr → Bool
      | [] => false
      | nx :: L =>
            match nx with
            | .node _ _ => true
            | .app f a => go (f :: a :: L)
            | .lam _ t b _ => go (t :: b :: L)
            | .forallE _ t b _ => go (t :: b :: L)
            | .letE _ t v b _ => go (t :: v :: b :: L)
            | .proj _ _ b => go (b :: L)
            | _ => go L
      go [E]


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


partial def CExpr.toExprF (E : CExpr) : Option Expr :=
      let rec go : List CExpr → List (Option Expr)
      | [] => []
      | nx :: L =>
            match nx with
            | .node _ _ => [.none]
            | .bvar i => .some (.bvar i) :: (go L)
            | .sort l => .some (.sort l) :: (go L)
            | .const n ll => .some (.const n ll) :: (go L)
            | .app f a =>
                  let r := go (f :: a :: L)
                  let F := List.headD r .none
                  let A := List.headD (List.drop 1 r) .none
                  match F, A with
                  | .some f', .some a' => .some (.app f' a') :: (List.drop 2 r)
                  | _ , _ => [.none]
            | .lam n t b i =>
                  let r := go (t :: b :: L)
                  let T := List.headD r .none
                  let B := List.headD (List.drop 1 r) .none
                  match T, B with
                  | .some t', .some b' => .some (.lam n t' b' i) :: (List.drop 2 r)
                  | _ , _ => [.none]
            | .forallE n t b i =>
                  let r := go (t :: b :: L)
                  let T := List.headD r .none
                  let B := List.headD (List.drop 1 r) .none
                  match T, B with
                  | .some t', .some b' => .some (.forallE n t' b' i) :: (List.drop 2 r)
                  | _ , _ => [.none]
            | .letE n t v b i =>
                  let r := go (t :: v :: b :: L)
                  let T := List.headD r .none
                  let V := List.headD (List.drop 1 r) .none
                  let B := List.headD (List.drop 2 r) .none
                  match T, V, B with
                  | .some t', .some v', .some b' => .some (.letE n t' v' b' i) :: (List.drop 2 r)
                  | _ , _, _ => [.none]
            | .lit l => .some (.lit l) :: (go L)
            | .proj t i b =>
                  let r := go (b :: L)
                  let B := List.headD r .none
                  match B with
                  | .some b' => .some (.proj t i b') :: (List.drop 1 r)
                  | _ => [.none]
            | .failed => [.none]
      List.headD (go [E]) .none



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


partial def CExpr.getNodesMaxIdxF (E : CExpr) : Option Nat :=
      let rec go : List CExpr → List Nat
      | [] => []
      | nx :: L =>
            match nx with
            | .node i _ => i :: (go L)
            | .app f a =>
                  let r := go (f :: a :: L)
                  let F := List.headD r 0
                  let A := List.headD (List.drop 1 r) 0
                  if F > A
                  then F :: (List.drop 2 r)
                  else A :: (List.drop 2 r)
            | .lam _ t b _ =>
                  let r := go (t :: b :: L)
                  let F := List.headD r 0
                  let A := List.headD (List.drop 1 r) 0
                  if F > A
                  then F :: (List.drop 2 r)
                  else A :: (List.drop 2 r)
            | .forallE _ t b _ =>
                  let r := go (t :: b :: L)
                  let F := List.headD r 0
                  let A := List.headD (List.drop 1 r) 0
                  if F > A
                  then F :: (List.drop 2 r)
                  else A :: (List.drop 2 r)
            | .letE _ t v b _ =>
                  let r := go (t :: v :: b :: L)
                  let T := List.headD r 0
                  let V := List.headD (List.drop 1 r) 0
                  let B := List.headD (List.drop 2 r) 0
                  if T > V
                  then  if B > T
                        then B :: (List.drop 3 r)
                        else T :: (List.drop 3 r)
                  else  if B > V
                        then B :: (List.drop 3 r)
                        else V :: (List.drop 3 r)
            | .proj _ _ b => go (b :: L)
            | _ => go L
      match (go [E]) with
      | [M] => .some M
      | _ => .none
