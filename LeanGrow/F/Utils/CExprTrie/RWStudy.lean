
import Mathlib.Tactic


open Lean Meta Mathlib Elab Tactic

-- # todo

#check MVarId.convert


#check CC.CCM.mkCongrProofCore


#check TermCongr.mkCongrOf

#check MVarId.revert

#check MVarId.revertAll

#check MVarId.congrN

#check withRWRulesSeq

#check MVarId.congrCore

#check Conv.congr



-- # congr

#check MVarId.congrCore!
-- repeatedly applyies passes replacing goal mvar with new one, adding internmediate goal ones ?
#check MVarId.congrPasses!
-- The passes are applications *some* of the following thms:

#check implies_congr
#check pi_congr
#check forall_prop_domain_congr
#check let_congr
-- and more fancier stuff, like:
#check MVarId.smartHCongr?




#check mkHCongrWithArity'

#check CongrState
