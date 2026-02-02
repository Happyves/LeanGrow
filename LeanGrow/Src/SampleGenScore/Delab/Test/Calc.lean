
/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.SampleGenScore.Delab.Calc

import Mathlib.Algebra.Ring.Int.Defs


open Lean Meta



def test_calc_sample (n : Name) : MetaM Unit := do
  let .some info := (← getEnv).find? n | throwError "Bad name"
  lambdaTelescope info.value! <| fun _ b => do
    let h := b.getAppFn'
    let as := b.getAppArgs
    let sub ← delabSample_Calc_core h as
    let sam ← delabSample_Calc_top (← getLCtx) (← getLocalInstances) h as
    match sub, sam with
    | .none, .none => IO.println "Not calc"
    | .none, .some sam => IO.println s!"Unexpected success of sam {← sam.pp} "
    | .some sub, .none => IO.println s!"Unexpected success of sub {← sub.mapM ppExpr} "
    | .some sub, .some sam =>
        IO.println s!"Sample {← sam.pp}\nNext:"
        for nex in sub do
          IO.println s!"Type: {← ppExpr (← inferType nex)}\nTerm: {← ppExpr ( nex)}"



theorem test_1 (a b c : Int) : (a + b)^2 + c = c + (a^2 + 2*b*a + b^2) := by
  calc
    (a + b)^2 + c = a^2 + 2*a*b + b^2 + c := by
      rw [@add_sq Int]
    _ = c + (a^2 + 2*a*b + b^2) := by
      rw [add_comm]
    _ = c + (a^2 + 2*b*a + b^2) := by
      rw [mul_assoc]
      rw [(show a*b = b*a by apply mul_comm)]
      rw [mul_assoc]

#print test_1

-- tracing_mode .std
-- tracing_flags [(`delabSample_Calc_top, TracingFlags.all)]

#eval test_calc_sample `test_1


#check 1

theorem test_2 (a b : Int) (hb : b > 0) : (a + b)^2 ≤ a^2 + 2*a*b + 2*(b^2) := by
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

#print test_2

#eval test_calc_sample `test_2


#check 1


theorem test_3 (a b c : Int) (hb : b > 0) (hc : c > 0)
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



#print test_3

tracing_mode .std
tracing_flags [(`delabSample_Calc_top, TracingFlags.all)]


#eval test_calc_sample `test_3


#check 1
