

import Lean

open Lean

#check MVarId.contradiction

#check Elab.Tactic.evalContradiction

/-

contradiction
| False.elim _ ((fvar : ¬ p) (fvar : p))
| absurd (Eq.refl _) (fvar : x ≠ x)
| mkNoConfusion
| absurd fvar (of_decide_eq_false _)

-/


#check absurd
#check of_decide_eq_false


-- Also do exfalso !


#check MVarId.exfalso

/-
False.elim _ mvar

-/


#check MVarId.byContra?
#check Decidable.byContradiction
#check Classical.byContradiction

/-

(Classical.byContradiction <|> Decidable.byContradiction) mvar
-/
