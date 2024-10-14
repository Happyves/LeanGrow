
import Lean

open Lean Meta

-- # Reduction

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
-- which does wierd envireonement extension stuff.
-- Maybe this extracts recursor from the `.match_1` type declarations that are generated from `match`
-- Proceeding, the number of arguments is compared to the number of
-- indices and discriminators provided by the `MatcherInfo`.
-- If there are to few, we return he `.partialApp` result
-- Otherwise, it gest wierd.
-- For what I can guess, the code that follows reduces the arguements further, with
#check whnf -- extern
-- and a final ↓ sprinkled on top
#check Expr.headBeta


-- We now study `reduceRec`.
-- We first get the number of required arguements with
#check RecursorVal.getMajorIdx
-- if not enough args are present (partial application), we run the fail function.
-- We then get the arguement that is beeing recursed on, which is called `major`
-- It is reduced with the extern `whnf`.
-- If the recursor is flaged with `k` (read good docs of ↓)
#check RecursorVal.k
-- Then we run
#check_failure Meta.toCtorWhenK
-- it does some prerocessing, checking if major's type is the constant
-- who's name is also the prefix of the recursor, and that major has not mvars
-- If checks pass, the returned value will be a constructor built from
#check_failure Meta.mkNullaryCtor
-- which gets the first constructor of the indcutive type we're working with via
#check_failure getFirstCtor
-- and appends the paramenters (.numParams) to it, into an application

-- Next, in `reduceRec`, we lift literals to atual expressions (Nat or String) with
#check Expr.toCtorIfLit
-- which is followed by a wierd post-process step for literal management:
#check_failure cleanupNatOffsetMajor
-- Next, we attempt to reduce possible structures, or pass majot to future steps, with
#check_failure toCtorWhenStructure
-- First we check that eta is configurated, and we're not dealing with a class, via
#check useEtaStruct
-- or that it is a applicaiton with a constructor head
#check isConstructorApp
-- We then check if the type of major is an application with a Prop as head
-- and finally, if not (no eta for propositions), we get the first (and only  should be `mk`) constructor
#check_failure getFirstCtor
-- with which we start building an applicaiton, by first adding he parameters, and then
-- adding the projections with
#check mkProjFn
-- This is implemented as follows, we get structure data with
#check getStructureInfo?
-- If no structure data is available, we return a `.proj _ _ major` expression, with
#check mkProj
-- If info is available, we get the fancy name of the projection, and build an applicaiton with
-- that projection as head, via
#check StructureInfo.getProjFn?
-- otherwise, we return `.proj _ _ major` as before


-- Next, in `reduceRec`, we try to find the appropriate branch to apply to the arguement.
-- To do so, we use:
#check_failure getRecRuleFor
-- ↑ get the head of major, check that its a constant and looks for a rule match that name via
#check RecursorVal.rules
#check RecursorRule.ctor
-- We then get the right hand-side of that rule with
#check RecursorRule.rhs
-- instantiat levels, and build a function application with rhs as head
-- an the argument of majors (up to a number : params+motives+minors)
-- Finally, we glue back all the remaining args


#check Quot.lift
#check Quot.ind
-- We now look at `reduceQuotRec`
-- As before, we get the major argument, reduce it with the external whnf
-- mjor should be a function application who's head is a
#check ConstantInfo.quotInfo
-- The relevant arguments and are extracted, using indices that are given
-- at the bottom of the implementation. The relevant parts are then glued back
-- together.




-- # Levels

-- We study
#check Core.instantiateValueLevelParams
-- a genuine use of it in the context of `whnfCore` is in
#check reduceMatcher?
-- Here, the levels its used with originate as follwos: they are the levels
-- of the constaant that is the head of the application that we are running `whnfCore` on.
-- The only reason that `Core.instantiateValueLevelParams` is in CoreM is so that we have
-- access to a cahce to consult. The real work is performed by
#check ConstantInfo.instantiateValueLevelParams!
-- which will run ↓ with the the added arguement of
#check ConstantInfo.levelParams
#check Expr.instantiateLevelParams
-- In the implementation of ↑, we have:
#check_failure Expr.getParamSubst
-- which basicly acts as a dictionary: it reads params and levels until it foudn the queried
-- param, at which stage it returns the corresponding level at that position in the level list
-- Then,
#check Expr.instantiateLevelParamsCore
-- expects a constant or a sort as arguement, and replaces parameters by levels
-- using the above function and
#check Level.substParams
-- TODO: finish




-- # Tests with RecursorVal


inductive testType (x : Nat) : String → List Nat → Type where
| fst (y : UInt16) : testType x "hello" []
| snd (z : UInt8) (w : Unit) : testType x "world" []
| thr : testType x "!" [42]

#check testType.rec

def RecValData : CoreM Unit := do
  let .some (.recInfo i) := (← getEnv).find? `testType.rec | throwError "ahh 1"
  IO.println s!"Names : {i.all} ; params : {i.numParams} ; indices : {i.numIndices} ; minors : {i.numMinors} ; motives {i.numMotives}"
  -- to study → rules

#eval RecValData


-- # Match expressions

def fib : Nat → Nat
| 0 => 0
| 1 => 1
| n+2 => fib (n+1) + fib n

--set_option pp.all true in
#print fib

#check fib.match_1
#print Nat.brecOn


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
