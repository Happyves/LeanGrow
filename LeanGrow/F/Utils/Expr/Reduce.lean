
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
-- The purpose of ↑, as the docs suggest is to make the constructor explicit in these cases,
-- so that we can perform the reuduction with  the further parts of `reduceRec`.
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

-- Note : I don't see how projection of structures work in this context ...


#check Quot.lift
#check Quot.ind
-- We now look at `reduceQuotRec`
-- As before, we get the major argument, reduce it with the external whnf
-- mjor should be a function application who's head is a
#check ConstantInfo.quotInfo
-- The relevant arguments and are extracted, using indices that are given
-- at the bottom of the implementation. The relevant parts are then glued back
-- together.


/-
Note:
The fact we don't δ reduce has consequences, for example in `Lean.Meta.isDefEqProjDelta` at `Lean > Meta > ExprDefEq`.
-/



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
  IO.println s!"Names : {i.all} ; params : {i.numParams} ; indices : {i.numIndices} ; minors : {i.numMinors} ; motives {i.numMotives}\n\n"
  IO.println s!"Rules {(i.rules.map (fun x => (repr x.ctor,  x.rhs)))}"
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
#print Nat.below


def test_m_1 : CoreM Unit := do
  let .some (.defnInfo i) := (← getEnv).find? `fib | throwError "ahh 1"
  IO.println s!"{repr i.value}"

#eval test_m_1


def test_m_2 : MetaM Unit := do
  let .some (.defnInfo i) := (← getEnv).find? `fib | throwError "ahh 1"
  IO.println s!"{(← reduce i.value)}"

#eval test_m_2


def myAdd (n : Nat) : Nat → Nat
| 0 => n
| m+1 => Nat.succ (myAdd n m)

#print myAdd.match_1
#print myAdd






-- # Structures

structure moreTest where
  a : Nat
  b : String

set_option pp.all true in
#print moreTest.a


def StructData : CoreM Unit := do
  let .some (.defnInfo i) := (← getEnv).find? `moreTest.a | throwError "ahh 1"
  IO.println s!"{repr i.value}"

#eval StructData

#check moreTest.rec



-- # Are def with prop types thms

def mydefthm (n m : Nat) : n = m := sorry

def test_mydefthm : CoreM Unit := do
  let .some (.thmInfo _) := (← getEnv).find? `moreTest.a | throwError "ahh 1"
-- It is defined as def despite having prop as type
-- #eval test_mydefthm


-- # Prop irrelevance in kernel

theorem p1 (n m : Nat) (h₁ : n = m) (h₂ : n = 42) : m = 42 := by
  rw [← h₁] ; exact h₂

theorem p2 (n m : Nat) (h₁ : n = m) (h₂ : n = 42) : m = 42 := by
  rw [eq_comm] ; rw [h₁] at h₂ ; exact h₂.symm

#print p1
#print p2

theorem p3 : p1 = p2 := rfl

set_option pp.all true in
#print p3

def fp (_ : ∀ (n m : Nat), n = m → n = 42 → m = 42) : Nat := 37

#check fp

example : fp p1 = fp p2 := rfl

theorem p1' : 1 < 3 := by
  apply Nat.lt_of_succ_lt_succ
  decide

theorem p2' : 1 < 3 := by
  rw [Nat.lt_succ]
  decide

#print p1'
#print p2'

theorem p3' : [1,2,3].get ⟨1, p1'⟩ = [1,2,3].get ⟨1, p2'⟩ := rfl

set_option pp.all true in
#print p3'


theorem p4 (h : [1,2,3].get ⟨1, p1'⟩ = 42) : [1,2,3].get ⟨1, p2'⟩ = 42 := by
  exact h


#print p4

-- # testing nabla

example : (fun n : Nat => n+2) = (fun x => (fun n : Nat => n+2) x) := rfl


-- # checking if lets in thm types

theorem p5 (n : Nat) (h : let x := 42 ; n = x) : let res := True ; res := sorry

#print p5


def test_p5 : CoreM Unit := do
  let .some (.thmInfo i) := (← getEnv).find? `p5 | throwError "ahh 1"
  IO.println s!"{repr i.type}"

#eval test_p5


-- # testing unfold declarations

#check getUnfoldEqnFor?
#check funext
#check getEqnsFor?


def test_6 : MetaM Unit := do
  let res ← getUnfoldEqnFor? `fib
  IO.println s!"{repr res}"

#eval test_6

def test_7 : MetaM Unit := do
  let res ← getEqnsFor? `fib
  IO.println s!"{repr res}"

#eval test_7

#check fib.eq_def

#check fib.eq_1
#check fib.eq_2
#check fib.eq_3

def test_8 : MetaM Unit := do
  let .some (.thmInfo i) := (← getEnv).find? `fib.eq_1 | throwError "ahh 1"
  IO.println s!"{repr i.type}\n\n\n{repr i.value}"

#eval test_8

#check Nat.add.eq_1
#check Nat.add.eq_2


def mutlimatch : Nat → Nat → Nat
| 0, 0 => 0
| _+1, 0 => 0
| 0, n+1 => n
| n+1, m+1 => n+m

#check mutlimatch.eq_1
#check_failure mutlimatch.eq_2
#check_failure mutlimatch.eq_1.eq_1
-- this is fixed in newer versions



-- # More on recursors

def test_9 : MetaM Unit := do
  let .some (.recInfo i) := (← getEnv).find? `Nat.rec | throwError "ahh 1"
  IO.println s!"{(i.rules.map (fun x => (x.ctor, x.rhs)))}"

#eval test_9


def test_10 : MetaM Unit := do
  let .some (.recInfo i) := (← getEnv).find? `Nat.rec | throwError "ahh 1"
  let rule_rhs := (i.rules.get! 1).rhs
  let test : Expr :=
    -- rule_rhs (fun _ => Nat) 1 (fun _ sofar => sofar+1)
    .app (.app (.app rule_rhs (.lam `x (.const `Nat []) (.const `Nat []) .default))
      (.app (.const `Nat.succ []) (.const `Nat.zero [])))
        (.lam `n (.const `Nat []) (.lam `sofar (.const `Nat []) (.app (.const `Nat.succ []) (.bvar 0)) .default) .default)
  IO.println s!"{← reduce test}" -- with `← whnf`, yields 1 for rule 0


#eval test_10


def testAdd2 (n : Nat) : Nat := @Nat.rec (fun _ => Nat) 2 (fun _ sofar => Nat.succ sofar) n

#check testAdd2.eq_1
-- no disjunction in newest version either
