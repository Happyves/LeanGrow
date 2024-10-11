
import Lean

#check 1

open Lean Meta

-- We have reduction in the form of
#check reduce
-- which seems to be iteration of `whnf` (from extern (kernel?)) on the term
-- and then on its arguments

-- There is a different implementation of weak head normal form.
#check whnfImp
-- It first tries to replace free ad meta variables from contexts in
#check whnfEasyCases
-- It also stores reduction results in a cache for future uses
#check_failure cache -- privtae
-- The main function for reduction is
#check whnfCore

-- ζ-reduction is handled via
#check Expr.instantiate1
-- β-reduction is handled via
#check Expr.betaRev
-- `match` expressions seem to be handled via
#check reduceMatcher?
-- ι-reduction is handled via
#check_failure reduceRec -- private
#check_failure reduceQuotRec -- private
-- And its performed in `whnfCore` if were're dealing with an application who's head is a
#check RecursorVal
#check QuotVal

/- We can see what is happening in `reduceRec`. The major index corresponds to the actal object we run recursion on.
We first reduce it with the C++ kernels whnf, then we use the follwoing to see which rule applies-/
#check_failure getRecRuleFor --private
/- which simply sooks at the application head of the argument, and tries to match it to a constructor, for which
it then returns the rules. Then, we flue the rest of the relevant arguments back with many `mkAppRange`-/


#print Nat.add

elab "test_4" : command => do
  let .defnInfo v := (← getEnv).constants.find! `Option.map | throwError "ahh 1" -- `Nat.add
  let r ← Elab.Command.liftTermElabM (@Lean.Meta.reduce v.value false true false)
  let s := (repr r)
  logInfo s

-- set_option pp.all true in
-- set_option pp.instances false in
test_4

set_option pp.all true in
#print Option.map
