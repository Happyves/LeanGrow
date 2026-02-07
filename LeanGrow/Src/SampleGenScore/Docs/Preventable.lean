

import Mathlib.Tactic

#check 1

-- for grind, linarith, ring & co, find ways to tell from Expr that tactic is applied...

open Lean Meta Elab Term Tactic Mathlib


-- `ring` is implemented by
#check Mathlib.Tactic.Ring.proveEq
-- and seems to always wrap the term in
#check Mathlib.Tactic.Ring.of_eq
-- example
theorem test_2 (x : Int) : (x +1)^2 = 1 + x^2 + 2*x := by ring
#print test_2

-- ring_nf and linarith are more complex ...
#check Mathlib.Tactic.Linarith.linarith


theorem test_1 (x y : Int)  (h1 : x + 1 ≥ 0) (h2 : 5 ≤ y)
  : x + y + 1 ≥ 5 := by
    linarith

#print test_1

#check Tactic.Linarith.lt_irrefl
-- has Mathlib prefix

theorem test_3 (x y : Int)  (h1 : x + 1 ≥ 0) (h2 : 5 ≤ y)
  : x + y + 1 ≥ 5 := by
    grind

#print test_3
#print test_3._proof_1_1
#check Grind.intro_with_eq

-- Lean prefix

theorem test_4 (x y : Int)  (h1 : x + 1 ≥ 0) (h2 : x = y)
  : y + 1 ≥ 0 := by
    grind

#print test_4
#print test_4._proof_1_1

#check List.perm_append_comm

-- simple rule would be to check if lemma has prefix `Mathlib.Tactic`
-- since a lot of tactics seem to do this

open List in
theorem test_5 : ∀ {n : Nat}, length (range' s n step) = n := by grind

#print test_5
#print test_5._proof_1_1
-- no grind lemmata
