
import Lean.Expr
import LeanGrow.F.Utils.List

import Lean --delete after tests
import Mathlib.Data.Nat.Factorization.Basic


open Lean



inductive LExpr where
| bvar (deBruijnIndex : Nat)
| fvar (fvarId : FVarId)
| mvar (mvarId : MVarId)
| sort (u : Level)
| const (declName : Name) (us : List Level)
| app
| lam (binderName : Name) (binderInfo : BinderInfo)
| forallE (binderName : Name) (binderInfo : BinderInfo)
| letE (declName : Name) (nonDep : Bool)
| lit (val : Literal)
| proj (typeName : Name) (idx : Nat)
deriving BEq, Inhabited, Repr


partial def Lean.Expr.linearize (e : Expr) : List LExpr :=
  let rec go : List Expr → List LExpr
    | [] => []
    | nx :: more =>
        match nx with
        | .bvar (deBruijnIndex : Nat) => .bvar (deBruijnIndex : Nat) :: go more
        | .fvar (fvarId : FVarId) => .fvar (fvarId : FVarId) :: go more
        | .mvar (mvarId : MVarId) => .mvar (mvarId : MVarId) :: go more
        | .sort (u : Level) => .sort (u : Level) :: go more
        | .const (declName : Name) (us : List Level) => .const (declName : Name) (us : List Level) :: go more
        | .app l r => .app :: go (l :: r :: more)
        | .lam (binderName : Name) l r (binderInfo : BinderInfo) => .lam (binderName : Name) (binderInfo : BinderInfo) :: go (l :: r :: more)
        | .forallE (binderName : Name) l r (binderInfo : BinderInfo) => .forallE (binderName : Name) (binderInfo : BinderInfo) :: go (l :: r :: more)
        | .letE (declName : Name) a b c (nonDep : Bool) => .letE (declName : Name) (nonDep : Bool) :: go (a :: b :: c :: more)
        | .lit (val : Literal) => .lit (val : Literal) :: go more
        | .proj (typeName : Name) (idx : Nat) e => .proj (typeName : Name) (idx : Nat) :: go (e :: more)
        | .mdata _ e => go (e :: more)
  go [e]


partial def LExpr.delinearize (L : List LExpr) : Expr :=
  let rec go : List LExpr → (Expr × List LExpr)
    | [] => panic! "aaahh"
    | nx :: more =>
        match nx with
        | .app =>
              let (f, next) := go more
              let (a, rest) := go next
              (.app f a, rest)
        | .lam (binderName : Name) (binderInfo : BinderInfo) =>
              let (f, next) := go more
              let (a, rest) := go next
              (.lam (binderName : Name) f a (binderInfo : BinderInfo), rest)
        | .forallE (binderName : Name) (binderInfo : BinderInfo) =>
              let (f, next) := go more
              let (a, rest) := go next
              (.forallE (binderName : Name) f a (binderInfo : BinderInfo), rest)
        | .letE (declName : Name) (nonDep : Bool) =>
              let (a, r1) := go more
              let (b, r2) := go r1
              let (c, r3) := go r2
              (.letE declName a b c nonDep, r3)
        | .proj (typeName : Name) (idx : Nat) =>
              let (a, r1) := go more
              (.proj (typeName : Name) (idx : Nat) a, r1)
        | .lit (val : Literal) => (.lit (val : Literal), more)
        | .bvar (deBruijnIndex : Nat) => (.bvar (deBruijnIndex : Nat), more)
        | .fvar (fvarId : FVarId)  => (.fvar (fvarId : FVarId), more)
        | .mvar (mvarId : MVarId) => (.mvar (mvarId : MVarId), more)
        | .sort (u : Level) => (.sort (u : Level), more)
        | .const (declName : Name) (us : List Level) => (.const (declName : Name) (us : List Level), more)

  (go L).1


def test_1 (n : Name) : CoreM Unit := do
  let env ← getEnv
  let .some info := env.find? n | throwError "aaah 1"
  let L := Lean.Expr.linearize info.type
  let D := LExpr.delinearize L
  IO.println s!"Vanilla:\n{repr info.type}\n\nLinearized:\n{repr L}\n\nDelinearized:\n{repr D}\n\nSame?\n → {info.type == D}"

lemma test_decl_1 : ∀ n : Nat, Prime n → ∀ m : Nat, Odd m → (h : Nat.Coprime n m) → ((fun (x y : Nat) (H : Nat.Coprime n m) => 1+1=2) 1 1 h) → Even m := sorry


#eval test_1 `test_decl_1
