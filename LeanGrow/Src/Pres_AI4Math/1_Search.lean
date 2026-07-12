
import LeanGrow.Src.Search.Frontend.Sandbox

import Mathlib.Data.List.Dedup

open List

set_option linter.style.longLine false


def stdSanbox := #[`List.dedup_cons_of_mem', `List.dedup_cons_of_not_mem', `List.length_append,
  `List.mem_dedup, `List.dedup_idem, `List.dedup_sublist, `List.dedup_subset, `List.length_erase_le, `List.Perm.dedup,
  `List.dedup]
  -- lemmata we allow in our search

def elimSandbox : Array Lean.Name := #[]
def funIndSandbox := #[`List.length]
-- additional induction principles we allow in our search

grow_load_sandbox stdSanbox ; elimSandbox ; funIndSandbox
-- loads the allowed theorems, does set-up


tracing_mode .std
tracing_flags [(`growImpl, [TracingFlags.zero, .one])]
-- will trace the search state



theorem test (l L : List Nat) (h : (l ++ L).length = 42) : (l.length + L.length) = 42 := by
  grows

#print test

theorem test_sol (l L : List Nat) (h : (l ++ L).length = 42) : (l.length + L.length) = 42 := by
  rw [← length_append]
  exact h

-- In this example, the term is close to the solution


theorem test' (l : List Nat) : l.dedup <+ l := by
  grows

#print test'

theorem test'_sol (l : List Nat) : l.dedup <+ l := by
  apply dedup_sublist

/-
In this example, the term is unecessrily complicated:
- we deduce `l.dedup <+ l` as a foward step, `g.1` in term
- we make the useless forward step `g.2 : l.dedup.Subset l`
- we then show `l.dedup <+ l → l.dedup.Subset l → l.dedup <+ l` by induction on `l`
  where in the base case and the step we simply apply the first hypothesis
- we use this result, applied to the foward steps, to complete the proof
-/
