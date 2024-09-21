import Mathlib.Tactic

open BigOperators




example (n : ℕ) : Even (∑ n in ((Finset.range n).filter Even), n) :=
  by
  induction' n with n ih
  · rw [Finset.range_zero]
    rw [Finset.filter_empty]
    rw [Finset.sum_empty]
    decide
  · rw [Finset.range_succ]
    rw [Finset.filter_insert]
    split_ifs with q
    · rw [Finset.sum_insert]
      · exact Even.add q ih
      · intro con
        rw [Finset.mem_filter] at con
        exact Finset.not_mem_range_self con.left
    · exact ih

#check Finset.range_zero
