import LeanGrow.F.Utils.CExprTrie.Types
import Lean
import LeanGrow.F.Data.CExpr.API
import Mathlib.Data.List.Sort
import LeanGrow.F.Data.CExpr.ReduceInferMuggle.Reduce

open Lean

#check 1

/-
We want:
- conservative conversion : if its supposed to replace unification, we shouldn't throw to many false
  positives, since it will be costly to propagate and analyse clashes for unification we expect to be
  false most of the time.
- liberal congruence : assuming the euqlities we see among goals aren't nonsensical most of the time
  (which is the job of conversion), liberal congruence should counter our lack of congruence closure
-/



/-
Conversion
- delta(-beta-iota ?)
- proof irrelevance
- count the appearance of pairs to convert : we seek large average appearances

-/


/-
Congruence

-/
