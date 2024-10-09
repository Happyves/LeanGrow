import LeanGrow.F.Utils.Expr.GetHyps
import LeanGrow.F.Data.BuildDAG.ofTypeExpr
import LeanGrow.F.Data.BuildDAG.SinksFirst
import LeanGrow.F.Data.Unification.EmbedRaw
import Lean
import Mathlib.Data.Nat.Factorization.Basic

open Lean


def fake_ltx : List (Nat × CExpr) :=
  [(0, .const `Nat []),
   (1, .const `Nat []),
   --(2, .app (.app (.app (.const `Eq [1]) (.const `Nat [])) (.node 0 (.ofBvar 37))) (.node 1 (.ofBvar 37)))
  ]

def fake_thm (n m : Nat) (h : n = m) : n = 42 := sorry

set_option pp.all true in
#print fake_thm

--#exit

def test_1 (n : Name) : CoreM Unit := do
  let env ← getEnv
  let .some info := env.find? n | throwError "aaah 1"
  let (hs,g) := Lean.Expr.getHypsGoal info.type
  let (hs, _) := ThmType_ToDAG hs hs.length g
  -- IO.println s!"{repr hs}\n"
  let sorted := SinksFirst hs
  -- IO.println s!"{repr sorted}\n"
  let (order, thmdata) := DAG_RawToFormat sorted hs.length
  -- IO.println s!"{repr order}\n"
  -- IO.println s!"{repr thmdata}\n"
  --let embeds := full_matcher_rawF thmdata order fake_ltx
  let embeds := partial_matcher_rawF thmdata order fake_ltx
  IO.println s!"{repr embeds}"

#eval test_1 `fake_thm
