

import LeanGrow.Src.SampleGenScore.Delab.Test.Simp
import LeanGrow.Src.SampleGenScore.Test.SampleBack
import LeanGrow.Src.SampleGenScore.Test.SampleConjable


-- # Generalisation heuristic: sampling

open List

theorem testProof (l L : List Nat) : l.dedup.dedup.length + L.length ≤ (l ++ L).length:= by
  rw [dedup_idem, length_append]
  apply Nat.add_le_add_right
  apply Sublist.length_le
  apply dedup_sublist


#eval testNoDelZet_B true `testProof 1 2 2

-- Get more samples by δing theorems

#eval testDelZet_B true `testProof 1 2 2 1 1



-- Simp

section Simp

open Set LinearMap Pointwise ConvexCone
variable {𝕜 R G M N O : Type*} [Semiring R] [PartialOrder R] [AddCommMonoid M] [SMul R M] {C : ConvexCone R M}

-- Easy

#print ConvexCone.pointed_iff_not_blunt

example : C.Pointed ↔ ¬ C.Blunt := by simp [Blunt, Pointed]

#eval testSimpDelab `ConvexCone.pointed_iff_not_blunt

-- With congruence

#print ConvexCone.coe_iInf

example {ι : Sort*} (f : ι → ConvexCone R M) : ↑(iInf f) = ⋂ i, (f i : Set M) := by
  simp [iInf]

#eval testSimpDelab `ConvexCone.coe_iInf


end Simp

-- "Conjecturables"

theorem testConj (n m : Nat) : n*m + 1 ≤ 2 + (m*n) := by
  calc
    n*m + 1 = m*n + 1 := by
      rw [Nat.mul_comm]
    _ = 1 + (m*n) := by
      rw [Nat.add_comm]
    _ ≤ 2 + (m*n) := by
      apply Nat.add_le_add_right
      decide


#eval testStd false `testConj 1 2 2

#eval testStd false `testConj 1 3 3
