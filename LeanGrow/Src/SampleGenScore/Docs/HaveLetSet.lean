
import Lean
import Mathlib.Tactic

open Lean Meta Elab Tactic


-- Very confused as what actually ends up elaborating `have`
#check Mathlib.Tactic.haveLetCore
-- have, let, suffices
-- or ↓ which is elaborated nowhere, it seems ...
#check Lean.Parser.Tactic.tacticHave__

theorem test (h : 2 = 2 → True) : True := by
  have : 2 = 2 := rfl
  exact h this

#eval return ((← getEnv).find? `test).get!.value!
-- It seems that have is elaborated as a `letE`

#check 1

#check Mathlib.Tactic.setArgsRest

#check evalSpecialize

/-

let
| let

have
| let
| (_ : ∀ _) term
| (_ : let _)

set
| rw[show (_ =_ ) from rfl] at * ; let _ ; have _ := rfl; ...

specialize
| (_ : ∀ _) (term)
↑ term is expected to be an app with fvar head
-/


#check evalRefine
