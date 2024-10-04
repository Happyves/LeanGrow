
import LeanGrow.F.Utils.Expr.GetHyps
import LeanGrow.F.Data.BuildDAG.ofTypeExpr
import Lean
import Mathlib.Data.Nat.Factorization.Basic

open Lean



def test_1 (n : Name) : CoreM Unit := do
  let env ← getEnv
  let .some info := env.find? n | throwError "aaah 1"
  let (hs,g) := Lean.Expr.getHypsGoal info.type
  IO.println s!"Hyps: {repr hs}\nGoal: {repr g}\n\n"
  let (hs, (g, gps)) := ThmType_ToDAG hs hs.length g
  IO.println s!"Found {hs.length} hyps:\n{repr hs}\nAnd goal {repr g}\nWith dependecies {gps}"

lemma test_decl_1 : ∀ n : Nat, Prime n → ∀ m : Nat, Odd m → (h : Nat.Coprime n m) → ((fun (x y : Nat) (H : Nat.Coprime n m) => 1+1=2) 1 1 h) → Even m := sorry

#eval test_1 `test_decl_1

lemma test_decl_2 : ∀ n : Nat, (h : ∀ i ∈ List.range n, i ≤ n) → n = 42 := sorry

#eval test_1 `test_decl_2
