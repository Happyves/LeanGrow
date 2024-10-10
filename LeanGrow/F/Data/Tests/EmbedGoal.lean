import LeanGrow.F.Utils.Expr.GetHyps
import LeanGrow.F.Data.BuildDAG.ofTypeExpr
import LeanGrow.F.Data.BuildDAG.SinksFirst
import LeanGrow.F.Data.Unification.EmbedGoal
import Lean
import Mathlib.Data.Nat.Factorization.Basic

open Lean


def fake_ltx_idx_cexpr : List (Array CExpr) :=
  [#[(.const `Nat []),
   (.const `Nat []),
   (.app (.app (.app (.const `Eq [1]) (.const `Nat [])) (.node 0 (.ofBvar 37))) (.node 1 (.ofBvar 37)))
  ]]

def fake_ltx_handler := fun n : Nat => (0,n)


def fake_goal : CExpr :=
  let fourty_two := (CExpr.app (CExpr.app (CExpr.app (CExpr.const `OfNat.ofNat [Lean.Level.zero]) (CExpr.const `Nat [])) (CExpr.lit (Lean.Literal.natVal 42))) (CExpr.app (CExpr.const `instOfNatNat []) (CExpr.lit (Lean.Literal.natVal 42))))
  (.app (.app (.app (.const `Eq [1]) (.const `Nat [])) (.node 0 (.ofBvar 37))) fourty_two)


def fake_thm (n m : Nat) (h : n = m) : n = 42 := sorry

set_option pp.all true in
#print fake_thm

--#exit

def test_1 (n : Name) : CoreM Unit := do
  let env ← getEnv
  let .some info := env.find? n | throwError "aaah 1"
  let (hs,g) := Lean.Expr.getHypsGoal info.type
  let (hs,(g,_)) := ThmType_ToDAG hs hs.length g
  --IO.println s!"{repr g}\n"
  let sorted := SinksFirst hs
  -- IO.println s!"{repr sorted}\n"
  let (_, thmdata) := DAG_RawToFormat sorted hs.length
  -- IO.println s!"{repr order}\n"
  -- IO.println s!"{repr thmdata}\n"
  let embed := match_goal thmdata fake_ltx_idx_cexpr fake_ltx_handler hs.length g fake_goal
  IO.println s!"{repr embed}"

-- #eval test_1 `fake_thm
