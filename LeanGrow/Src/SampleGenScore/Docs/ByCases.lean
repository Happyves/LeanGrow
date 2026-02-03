
import Lean


#check Lean.MVarId.byCases
#check Lean.MVarId.byCasesDec


/-

bycases
| (fun x : p ∨ ¬ p => cases(x)) (Classical.em p)
| (fun x : Decidable p => cases(x)) dec
-/


#check Decidable
#check Classical.em

#check dite_eq_ite
-- folder of ↑ contains macro for by_cases

theorem test_1 (n : Nat) : 42 = 42 := by
  by_cases n = 3
  · rfl
  · rfl


#print test_1
