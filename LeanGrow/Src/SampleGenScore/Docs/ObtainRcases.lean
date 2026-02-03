
import Lean

open Lean

example (f : ∃ x : Nat, 2 = 2) : 2 = 2 := by
  obtain ⟨a,b⟩ := f
  exact b

#check_failure Lean.Elab.Tactic.RCases.evalObtain
#check Elab.Tactic.RCases.rcases
-- all in file ↑


#check_failure Elab.Tactic.RCases.obtainNone
-- asserts the type which is given as new subgoal, intros the assert-goal and
-- runs rcases on the introed assert-goal

/-

obtain
| (fun fvar => rcases(fvar)) mvar
  -- actually, this seems to be betaed at some point ...
  -- there is a whnf in rcases !
| rcases(term)

rcases
| rcasesCore
| (rcasesCore : ∀ _) term+   -- due to generalise


rcasesCore
| cases -- via `MVarId.cases`
| (Quot.ind (β := fun _ => term) mvar terget_term : ∀ ...) term* -- revert, then
| substEq >>= rcases


rintro
| fun _ => rintro
| let _ := _ ; rintro
| substEq >>= rintro
| rcasesCore >>= rintro

-/


#check Quot.ind




#check Lean.Elab.Tactic.RCases.rintro


theorem test : ∀ x : Nat × Nat, 42 = 42 := by
  rintro ⟨a,b⟩
  rfl

#print test


theorem test_1 (x : Nat × Nat) : 42 = 42 := by
  obtain ⟨a,b⟩ := x
  rfl

#print test_1

theorem test_2  : 42 = 42 := by
  obtain ⟨a,b⟩ : Nat × Nat
  · exact (1,2)
  · rfl

#print test_2

theorem test_3  : 42 = 42 := by
  obtain ⟨a,b⟩ : Σ n : Nat, Fin n
  · refine ⟨1,?_⟩
    refine ⟨0,?_⟩
    decide
  · rfl

#print test_3


theorem test_4 (x : Nat × Nat) (h : x.1 = 37) : 42 = 42 := by
  rcases x with ⟨a,b⟩
  rfl

#print test_4

@[reducible]
def myMod (n : Nat) := Quot (fun x y : Nat => x % n = y % n)

#check Quot.ind


theorem test_5 (x : myMod 3) (hx : x = Quot.mk _ 42) : x = Quot.mk _ 42 := by
  -- apply Quot.ind _ x
  rcases x
  exact hx

#print test_5
