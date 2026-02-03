

import Mathlib.Tactic

#check 1

-- for linarith, ring & co, find ways to tell from Expr that tactic is applied...

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


-- simple rule would be to check if lemma has prefix `Mathlib.Tactic`
-- since a lot of tactics seem to do this
