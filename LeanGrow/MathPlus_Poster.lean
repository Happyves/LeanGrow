import Mathlib.Tactic

open BigOperators




example (n : ℕ) : Even (∑ m in ((Finset.range n).filter Even), m) :=
  by
  induction' n with n ih
  rw [Finset.range_zero]
  rw [Finset.filter_empty]
  -- Even (∑ n ∈ ∅, n)
  rw [Finset.sum_empty]
  -- ⊢ Even 0
  decide
  · /-
    n : ℕ
    ih : Even (∑ n ∈ Finset.filter Even (Finset.range n), n)
    ⊢ Even (∑ n ∈ Finset.filter Even (Finset.range (n + 1)), n)
    -/
    rw [Finset.range_succ]
    -- ⊢ Even (∑ n ∈ Finset.filter Even (insert n (Finset.range n)), n)
    rw [Finset.filter_insert]
    /-
    ⊢ Even (∑ n ∈ if Even n then insert n (Finset.filter Even (Finset.range n))
        else Finset.filter Even (Finset.range n), n)
    -/
    split_ifs with q
    · /-
      q : Even n
      ⊢ Even (∑ x ∈ insert n (Finset.filter Even (Finset.range n)), x)
      -/
      rw [Finset.sum_insert]
      · -- ⊢ Even (n + ∑ x ∈ Finset.filter Even (Finset.range n), x)
        exact Even.add q ih
      · -- ⊢ n ∉ Finset.filter Even (Finset.range n)
        intro con
        /-
        con : n ∈ Finset.filter Even (Finset.range n)
        ⊢ False
        -/
        rw [Finset.mem_filter] at con
        -- con : n ∈ Finset.range n ∧ Even n
        exact Finset.not_mem_range_self con.left
    · -- ⊢ Even (∑ x ∈ Finset.filter Even (Finset.range n), x)
      exact ih

#check Finset.range_zero


variables (X Y Z : Type)
    [TopologicalSpace X]
    [TopologicalSpace Y]
    [TopologicalSpace Z]

variables (f : X → Y) (g : Y → Z)

example
    (hf : Continuous f)
    (hg : Continuous g) :
    Continuous (g ∘ f) :=
    by
    constructor
    intros U hU
    let V := g⁻¹' U
    have hV : IsOpen V := by
      apply hg.isOpen_preimage
      assumption
    exact hf.isOpen_preimage V hV
