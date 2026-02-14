

import LeanGrow.Src.SampleGenScore.Gen.TestTools_SampleConj

import Mathlib.Data.List.Dedup
import Mathlib.Algebra.Ring.Int.Defs



open Lean Meta


def test (thmNames : Array Name) :=
  test_conjSample_cvbThm_S
    thmNames 1 2 2 .none .none
    (fun w tot _ T _ => (w.toFloat / tot.toFloat ≥ 0.33) && (T != .sort 0))
    (fun w tot _ _ => (w.toFloat / tot.toFloat ≥ 0.33))

#check 1

def test_samples (dbg : Bool) (thmNames : Array Name) : MetaM Unit := do
  let env ← getEnv
  let preS ← mkPreProCongr
  let mut L1 := ← getLCtx
  let mut L2 := ← getLocalInstances
  let mut samples : ListProd4 SampleData (List FVarId) Expr (List Expr) := .nil
  for thmName in thmNames do
    let .some (.thmInfo I) := env.find? thmName | throwError "Bad name"
    let .mk p fvs l1 l2 ← LambdaLetTelescope I.value 0 L1 L2
    let .mk res _ l1 l2 ← sampleCoreBack preS .empty l1 l2 1 2 2 .none .none (.cons (.raw p) (fvs.map Expr.fvarId!).toList .nil) samples .nil
    samples := res
    L1 := l1
    L2 := l2
  samples := if dbg then samples else samples.foldl .nil (fun w x y z L => match w with | .thmC .. => ListProd4.cons w x y z L | _ => L)
  withLCtx L1 L2 <| do
    samples.foldlM () (fun kind _ goal hyps _ => do
      IO.println "\nSample (back):"
      IO.println s! "Goal: {← ppExpr goal}"
      IO.println "Hyps:"
      hyps.foldlM (fun _ subp => do IO.println s!" · {← ppExpr subp}") ()
      IO.println s!"Kind: {← kind.pp}"
      )

#check 1

open List

theorem material_1 (l L : List Nat) : l.dedup.dedup.length + L.length ≤ (l ++ L).length:= by
  rw [dedup_idem]
  by_cases q : l = []
  · rw [q]
    dsimp
    rw [Nat.zero_add]
  · rw [length_append]
    apply Nat.add_le_add_right
    apply Sublist.length_le
    apply dedup_sublist


theorem material_2 (l L : List Nat) : l.dedup.dedup.length + L.length ≤ (l ++ L).length:= by
  rw [dedup_idem]
  rw [length_append]
  apply Nat.add_le_add_right
  by_cases q : l = []
  · rw [q]
    dsimp
    apply le_refl
  · apply Sublist.length_le
    apply dedup_sublist


theorem material_3 (l L : List Nat) : l.dedup.dedup.length + L.length ≤ (l ++ L).length:= by
  rw [dedup_idem]
  rw [length_append]
  apply Nat.add_le_add_right
  apply Sublist.length_le
  by_cases q : l = []
  · rw [q]
    dsimp
    rfl
  · apply dedup_sublist


def thmNames_1 := #[`material_1, `material_2, `material_3]

--samples
-- #eval test_samples true thmNames_1
-- sample bugs ...


theorem material_4 (a b c : Int) : (a + b)^2 + c = c + (a^2 + 2*b*a + b^2) := by
  calc
    (a + b)^2 + c = a^2 + 2*a*b + b^2 + c := by
      rw [@add_sq Int]
    _ = c + (a^2 + 2*a*b + b^2) := by
      rw [add_comm]
    _ = c + (a^2 + 2*b*a + b^2) := by
      rw [mul_assoc]
      rw [(show a*b = b*a by apply mul_comm)]
      rw [mul_assoc]



theorem material_5 (a b : Int) (hb : b > 0) : (a + b)^2 ≤ a^2 + 2*a*b + 2*(b^2) := by
  calc
    (a + b)^2 = a^2 + 2*a*b + b^2  := by
      rw [@add_sq Int]
    _ ≤ a^2 + 2*a*b + 2*(b^2) := by
      apply Int.add_le_add_left
      calc
        b^2 = 1*(b^2) := by
          rw [one_mul]
        _ ≤ 2*(b^2) := by
          rw [Int.mul_le_mul_right]
          · decide
          · apply Int.pow_pos hb


theorem material_6 (a b c : Int) (hb : b > 0) (hc : c > 0)
  : a^2 + 2*a*b + b^2 < a^2 + 2*a*b + 2*(b^2) + c := by
  calc
    a^2 + 2*a*b + b^2  ≤ a^2 + 2*a*b + 2*(b^2) := by
      apply Int.add_le_add_left
      calc
        b^2 = 1*(b^2) := by
          rw [one_mul]
        _ ≤ 2*(b^2) := by
          rw [Int.mul_le_mul_right]
          · decide
          · apply Int.pow_pos hb
    _ < a^2 + 2*a*b + 2*(b^2) + c := by
      apply Int.lt_add_of_pos_right
      exact hc


def thmNames_2 := #[`material_4, `material_5, `material_6]

--samples
-- #eval test_samples false thmNames_2


-- #eval test thmNames_2


/-
TODO
- query conj (+lg embed and non-lg-embed)
- caching
- dbg
- test query

-/
