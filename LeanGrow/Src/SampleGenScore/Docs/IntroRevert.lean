
import Lean
import Mathlib.Tactic


open Lean Meta Elab Tactic


#check evalIntro

#check MVarId.intro

#check Meta.substEq
-- tries to wrap the introed hyp with
#check heqToEq
-- and replaces the goal by reverting this new eq via
#check MVarId.assert
-- and proceeds as when heqToEq didn't apply, ie with
#check substCore


/-

intro
| term
| fun => intro
| let intro
| substEq

-/



#check evalRevert
#check MVarId.revert

/-

assert
| (term : ∀ ...) term

define
| (term : let ...)


revert
| (term : ∀ ... let ...) term+

↑ term need not be intro ; for example, for induction
-/


-- context

#check MVarId.assert
#check MVarId.withReverted

#check eq_of_heq
#check Eq.rec
#check Eq.ndrec


#check evalSpecialize
-- assert + intro
