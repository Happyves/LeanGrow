

import LeanGrow.Src.SampleGenScore.Delab.Test.Basic
import Mathlib.Tactic


open Lean


theorem tesT_1 (h : n+m = 42) : m+n = 42 :=
  Nat.add_comm n m ▸ h

#print tesT_1

-- #eval test_apply_sample `tesT_1
-- #eval test_apply_dig `tesT_1
-- #eval test_apply_top `tesT_1


theorem tesT_2: m+n + 42 = n+m + 42 :=
  congrArg (· + 42) (Nat.add_comm m n)

#print tesT_2

-- #eval test_apply_sample `tesT_2
-- #eval test_apply_dig `tesT_2
-- #eval test_apply_top `tesT_2


theorem tesT_3 (x : Int) : (x +1)^2 = 1 + x^2 + 2*x := by ring

#print tesT_3

-- #eval test_apply_sample `tesT_3
-- #eval test_apply_dig `tesT_3
-- #eval test_apply_top `tesT_3


theorem tesT_4 (x y : Int)  (h1 : x + 1 ≥ 0) (h2 : x = y)
  : y + 1 ≥ 0 := by
    grind

#print tesT_4

-- #eval test_apply_sample `tesT_4
-- #eval test_apply_dig `tesT_4
-- #eval test_apply_top `tesT_4
