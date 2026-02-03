
import Lean

open Lean Meta Elab Tactic

#check injectionCore
#check MVarId.acyclic
#check mkNoConfusion
#check Meta.mkNoConfusion

/-

injection
| injectionCore
| injectionCore >>= injectionIntro

injectionIntro
| (fun => injectionIntro)
| (fun _ => injectionIntro) (eq_of_heq fvar)


injectionCore
| mkNoConfusion
| mkNoConfusion terms*

mkNoConfusion
| False.elim _ (noConfusion_of_Nat terms*)
| noConfusionName terms*

acyclic
| False.elim _ ((Nat.lt_irrefl (SizeOf.sizeOf terms*)) (Nat.lt_of_lt_of_eq (...)))
-- ↑ should be enough to parse it ...

-/

#check noConfusion_of_Nat
#check Nat.lt_irrefl
#check Nat.lt_of_lt_of_eq
#check SizeOf.sizeOf
