
import LeanGrow.Src.Search.Frontend.Sandbox

import Mathlib.Data.List.Dedup

open List

set_option linter.style.longLine false


def stdSanbox := #[`List.dedup_cons_of_mem', `List.dedup_cons_of_not_mem', `List.length_append,
  `List.mem_dedup, `List.dedup_idem, `List.dedup_sublist, `List.dedup_subset, `List.length_erase_le, `List.Perm.dedup,
  `List.dedup]

def elimSandbox : Array Lean.Name := #[]

def funIndSandbox := #[`List.length]

grow_load_sandbox stdSanbox ; elimSandbox ; funIndSandbox

#check 1

tracing_mode .std
tracing_flags [(`growImpl, [TracingFlags.zero, .one]),
                ]

def Even (n : Nat) : Prop := ∃ k, n = 2*k


theorem test (l L : List Nat) (h : Even (l ++ L).length) : Even (l.length + L.length) := by
  grows -- yay

#print test

theorem test_sol (l L : List Nat) (h : Even (l ++ L).length) : Even (l.length + L.length) := by
  rw [← length_append]
  exact h

#print test_sol




theorem test' (l : List Nat) : l.dedup <+ l := by
  grows -- yay

#print test'

theorem test'_sol (l : List Nat) : l.dedup <+ l := by
  apply dedup_sublist
