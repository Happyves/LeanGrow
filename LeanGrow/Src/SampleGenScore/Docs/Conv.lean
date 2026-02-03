
import Lean


open Lean Meta Elab Tactic


#check Conv.evalConv
#check Eq.mp
#check Eq.mpr

/-

conv
| (_ : ∀ .. let) term* (Eq.mp convert fvar) -- at hyp
| Eq.mpr (id convert) mvar

To big .. has congr, simp, rw and much more

-/
