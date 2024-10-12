
import Lean

#check 1

open Lean Meta


-- We study
#check whnfCore
-- which starts with
#check whnfEasyCases
-- ↑ stops and returns ∀ λ Sort and lit, and replaces let-bound fvars and assigned mvars by their value
-- for lets, apps, constants and projections, it applies another function,
-- which corresponds to the next pieces of code of `whnfCore`
-- Bizarely, in this precise code that follows, constants are left untouched.
-- Lets n the other hand, are reduced (provided the config says so) to
#check Expr.instantiate1

-- Finally, in the case of apps, the interesting things happen
-- First, we check if the appli is a letFun
#check letFun -- exists out of tech dept ? or deeper purpose ?
#check Expr.letFunAppArgs?
-- and if so, we prefor ζ with
#check Expr.instantiate1
-- Next, we test for β by getting the head and checking if its a λ
#check Expr.isLambda
#check Expr.getAppRevArgs
-- then reduce with
#check Expr.betaRev
-- Finally, ι is tried on the whole expression via
#check Meta.reduceMatcher?
-- which can have a reduced output `.reduced` where the reduced expression is returned or
-- two fialed outputs `.partialApp` and `.stuck` where the expression is returned as is
-- There is a fourth option `noMatcher`, in which the expression is processed futher.
-- Strangly, that process involves getting the constant head info, and perfroming the
-- following depending on that info, which amounts to further variants of ι ??
#check_failure reduceRec -- private
#check_failure reduceQuotRec -- private

-- In the last case of `whnfCore`, we deal with projections
-- If the configurations allow, we first reduce the body of the projection.
-- Then, we apply the following to the result
#check projectCore?
-- If it ouputs none, we actually revert to the initial input expression to `whnfCore`
-- else, we keep reducing.

-- As the docs of `whnfCore` suggest, we indeed do not apply δ
-- This version, on the other hand, does:
#check whnfImp
-- δ occurs in
#check Meta.unfoldDefinition?
-- It only occurs if the constant is the head of an application,
-- and some caching and universe level management system is used.


-- Full reduction is performed by
#check reduce
-- It runs whnf, then perfroms reduction (not just whnf) on every argument in an application
-- If the result was a ∀, λ or projection, reduction is performed on the body (not binders, interestingly)


-- We now study `reduceMatcher?`
-- If the input isn't a constant head of an appli, or that constant isn't decalred as a matcher,
-- we output `.notMatcher`. Finding out if its a matcher is done by
#check getMatcherInfo?
-- aka.
#check Match.Extension.getMatcherInfo?
-- which does wier envireonement extension stuff
-- Proceeding, the number of arguments is compared to the number of
-- indices and discriminators provided by the `MatcherInfo`.
-- If there are to few, we return he `.aprtialApp` result





-- # To study

#check Core.instantiateValueLevelParams

#check Expr.toCtorIfLit
-- very important ! otherwise, `.lit 2` whouldn't work with `Nat.rec`



#exit

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
