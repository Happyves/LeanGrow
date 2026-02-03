
import Mathlib.Tactic


open Lean Elab Tactic Meta


#check substCore


/-

subst
| substEq
| (fun (_ = _) => (subst <|> substVar) ) (eq_of_heq fvar)
| substVar

substEq
| substCore
| (fun (_ = _) => substCore) term


substVar
| substCore

substCore
| ((fun _ =>)* substCore_postRev) fvars*
-- where ↑ should have 2, possibly more then ↑

substCore_postRev
| (Eq.rec <|> Eq.ndrec) ((fun _ =>)* next_proof) (Eq.symm? fvar)

-/

#check Eq.rec

#check Eq.ndrec
