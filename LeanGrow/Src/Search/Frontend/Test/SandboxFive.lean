

import Mathlib.Data.Nat.Choose.Bounds


import LeanGrowBeta.Frontend.Sandbox



def stdSanbox := #[ ``le_div_iff₀', ``Nat.descFactorial_eq_factorial_mul_choose,
  ``Nat.descFactorial_le_pow , ``Nat.factorial_pos , ``Nat.choose_eq_descFactorial_div_factorial,
  ``Nat.div_le_self, ``Nat.choose_le_descFactorial, ``LE.le.trans, ``div_le_iff₀',
  ``Nat.pow_sub_le_descFactorial, ``Nat.choose_eq_zero_of_lt, ``Nat.zero_le,
  ``zero_add, ``Nat.choose_succ_self_right, ``pow_zero, ``le_refl,
  ``Nat.lt_add_left_iff_pos, ``not_lt, ``Nat.le_zero_eq , ``Nat.choose_self ,
  ``Nat.choose_zero_right,
  ``Nat.one_le_two_pow, ``Nat.choose_succ_succ', ``Nat.two_pow_succ, ``Nat.add_le_add,
  ``Nat.choose_succ_le_two_pow, ``lt_of_le_of_lt, ``Nat.two_pow_pred_lt_two_pow,
  ``Nat.sub_add_cancel]

def elimSandbox : Array Lean.Name := #[]

def funIndSandbox : Array Lean.Name := #[]

-- grow_load_sandbox stdSanbox ; elimSandbox ; funIndSandbox

tracing_mode .std
tracing_flags [(`growImpl, TracingFlags.all)]


variable {α : Type*} [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]
open Nat

theorem test_1_sol (r n : ℕ) : (n.choose r : α) ≤ (n ^ r : α) / r ! := by
  rw [le_div_iff₀']
  · norm_cast
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact n.descFactorial_le_pow r
  exact mod_cast r.factorial_pos

lemma test_2_sol (n k : ℕ) : n.choose k ≤ n.descFactorial k := by
  rw [choose_eq_descFactorial_div_factorial]
  exact Nat.div_le_self _ _


lemma test_3_sol (n k : ℕ) : n.choose k ≤ n ^ k :=
  (choose_le_descFactorial n k).trans (descFactorial_le_pow n k)

theorem test_4_sol (r n : ℕ) : ((n + 1 - r : ℕ) ^ r : α) / r ! ≤ n.choose r := by
  rw [div_le_iff₀']
  · norm_cast
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact n.pow_sub_le_descFactorial r
  exact mod_cast r.factorial_pos

theorem test_5_sol (n k : ℕ) : (n + 1).choose k ≤ 2 ^ n := by
  by_cases lt : n + 1 < k -- grow can't do this
  · simp only [choose_eq_zero_of_lt lt, zero_le]
  · cases n with
    | zero =>
        cases k with
        | zero => simp only [zero_add, choose_succ_self_right, pow_zero, le_refl]
        | succ k => simp_all only [zero_add, Nat.lt_add_left_iff_pos, not_lt, le_zero_eq,
              choose_self, pow_zero, le_refl]
    | succ n =>
      rcases k with - | k
      · rw [choose_zero_right]
        exact Nat.one_le_two_pow
      · rw [choose_succ_succ', two_pow_succ]
        exact Nat.add_le_add (choose_succ_le_two_pow n k) (choose_succ_le_two_pow n (k + 1))

theorem test_6_sol (n k : ℕ) (p : 0 < n) : n.choose k < 2 ^ n := by
  refine lt_of_le_of_lt ?_ (Nat.two_pow_pred_lt_two_pow p)
  rw [← Nat.sub_add_cancel p]
  exact choose_succ_le_two_pow (n - 1) k
