
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

#check isAuxRecursor
#eval (do return isAuxRecursor (← getEnv) `Nat.recAux : CoreM _)
#eval (do return isAuxRecursor (← getEnv) `Nat.rec : CoreM _)
#eval (do return isAuxRecursor (← getEnv) `Nat.recOn : CoreM _)
#eval (do return isRecCore (← getEnv) `Nat.recAux : CoreM _)
#eval (do return isRecCore (← getEnv) `Nat.rec : CoreM _)



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
#check_failure fac.match_1.eq_1

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


def test4 (n : Nat) : Int := n

#print test4

#check congrArg

#eval getEqnsFor? `fac
#eval getEqnsFor? `a true
#eval getUnfoldEqnFor? `fac
#eval getUnfoldEqnFor? `a
#eval getUnfoldEqnFor? `a true


elab "redGoal" : tactic => do
  let t ← Elab.Tactic.getMainTarget
  let T ← whnf t
  let τ ← reduce t false false false
  logInfoAt (← getRef) s!"whnf: {(← ppExpr T)}\nreduced: {← ppExpr τ}"

--#exit

example : ∀ (n : ℕ), fac n ≥ 1 :=
  fun n ↦ Nat.recAux
    (le_refl 1)
    (fun n ih ↦ by
      have := le_trans ih (Nat.le_mul_of_pos_left (fac n) (Nat.succ_pos n))
      redGoal
      exact this
      ) n

def test5 := Nat.succ ((fun _ => 42) ())

#print test5

#check funext

@[ext] -- also generates ex_iff !
structure test6 where
  a : Nat
  b : Int

#check test6.ext
#print test6.ext
-- but this isn't done by kernel, so shows up in samples ?

#eval getEqnsFor? `test6 true
#eval getUnfoldEqnFor? `test6 true

#eval (do IO.println (Match.matchEqnsExt.getState (← getEnv) |>.eqns).toList : MetaM _)

#check PHashSet.toList

#check test6.mk


example : test6.a (test6.mk 1 2) = 1 := rfl

#exit


def fib : Nat → Nat
| 0 => 1
| 1 => 1
| n+2 => fib n.succ + fib n

theorem test2 (n : Nat) : fib n ≥ 1 := by
  induction' n with n ih
  · apply le_refl
  ·
