
import LeanGrow.F.Prototypes.MarkTwo.Frontend
import LeanGrow.F.Prototypes.MarkTwo.TestTypes

#check 1


example (r : myNat) : myAdd .z (myAdd .z r) = r :=
  Eq.trans (myAdd_zero (myAdd .z r)) (myAdd_zero r)

-- example (r : myNat) : (myAdd .z r) = r := by
--   grow
--   sorry

open Lean

elab "test" : command => do
  let env ← getEnv
  let stuff ←  env.constants.map₁.foldM (fun sofar x _ => do return (x) :: sofar) []
  IO.println (stuff.take 10)

--test
-- crashed infoview du to size ??

-- example (r : myNat) (h : myAdd .z (myAdd .z r) = (myAdd .z r)) : myAdd .z (myAdd .z r) = r := by
--   grow
--   sorry

#check 1

example (r : myNat) : myAdd .z (myAdd .z r) = r := by
  grow
  sorry

#check 1

-- TODO : propagate universes properly, because unification in ↑ fails because of this
