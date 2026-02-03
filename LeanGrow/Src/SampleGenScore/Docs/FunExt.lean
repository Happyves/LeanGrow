
import Lean
import Mathlib.Tactic


open Lean Meta Elab Term Tactic


example (f : Nat → Nat) : f = Nat.succ := by
  funext x -- a macro for apply funext
  sorry

example (f : Set Nat) : f = ∅ := by
  ext x -- a macro for apply funext
  sorry


#check Ext.extCore
-- in Lean/Elab/Tactic/Ext
#check Ext.getExtTheorems

-- ext seems to repeatedly try intro and `apply`ing ext theorems via
#check Ext.applyExtTheoremAt
