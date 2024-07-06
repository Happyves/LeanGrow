
import Lean
import Mathlib

open Lean


/-
The idea is to abstract types/sorts and instances on them, in a local context.
To perform `grow` we first generalise the local context, so that theorems that are
polymorphic in nature may apply. Seeing as in the final output, we only compose a
theorem with the default arguments, this will work in the initial local context, as
implicit arguments and instances will be synthesied anyway.

Maybe modify `CExpr.Match` with `node i, expr` assining node i to the expression ?
Then `List.length : \all a : Type, \all L : List a, Nat ` would apply to (l : List Nat),
assigning the node 0 corresponding to `a` to Nat IF THE LIST IS EMBEDDED FIRST. Otherwise,
the `Type` will fail to be embedded and the embedding attempt will stop !
So we embed the theorem in the LCtx and the constants of the environement.

Maybe



IMPORTANT OBSERVATIONS:

- `Nat.add_comm` will not be recognized on ltx (n : Nat) (h : n + 37 = 42), because we can't map its two Nats to the same Nat, at this stage.

- `Nat.eq_of_succ_eq` (is it ?) will not be recognized on ltx (n : Nat) (h : n + 1 = 42), for the same reason.

- Are the above two eve true ???

- We must handle instances, as they may not always be implicitly present in LCtx.
  For example, if we want to find `Finset.filter` at (l : Finset ℕ) (p : ℕ → Prop)

-/

#check List.filter
#check Finset.filter
#print DecidablePred
