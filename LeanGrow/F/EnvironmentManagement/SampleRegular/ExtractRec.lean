
import Lean
import Mathlib.Tactic
import Mathlib.Data.List.Basic

open Lean Meta


theorem test : n + 0 = n := by
  induction' n with n _
  · rfl
  · rfl

#print test

#check Nat.recAux
#check Nat.casesAuxOn
#check_failure List.recAux


def fac : Nat → Nat
| 0 => 1
| n+1 => n.succ * fac n

theorem test2 (n : Nat) : fac n ≥ 1 := by
  induction' n with n ih
  · apply le_refl
  · --unfold fac
    apply le_trans ih
    apply Nat.le_mul_of_pos_left
    apply Nat.succ_pos

#print test2
-- if `unfold` is kept, we get `fac.eq_def`
-- `dsimp ` adds nothing

#check fac.eq_def
#check fac.match_1

#print fac

#check fac.eq_1
#check fac.eq_2

#check_failure fac.match_1.eq_def

def a := 42

#check a.eq_def

theorem test3 : ∀ (n : ℕ), fac n ≥ 1 :=
  fun n ↦ Nat.recAux
    (le_refl 1)
    (fun n ih ↦ by
      have := le_trans ih (Nat.le_mul_of_pos_left (fac n) (Nat.succ_pos n))
      -- type of subexpr won't match goal
      exact this
      ) n


#exit

def fib : Nat → Nat
| 0 => 1
| 1 => 1
| n+2 => fib n.succ + fib n

theorem test2 (n : Nat) : fib n ≥ 1 := by
  induction' n with n ih
  · apply le_refl
  ·
