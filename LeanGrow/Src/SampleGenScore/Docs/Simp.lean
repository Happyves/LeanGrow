
import Lean
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.SimpIntro

import Mathlib.Geometry.Convex.Cone.Basic

-- #exit

open Lean Elab Tactic Meta Simp


#check Lean.Parser.Tactic.simp
#check Lean.Parser.Tactic.simpAll
#check Lean.Parser.Tactic.dsimp


#check evalSimp
#check evalSimpAll
#check evalDSimp

-- all of them start by making a context
#check mkSimpContext
-- that is made up of
#print Simp.Context
#print Simp.SimprocsArray
#print Simp.DischargeWrapper
#check MkSimpContextResult.simpArgs

-- It builds the context with:
#check_failure mkDischargeWrapper -- private ; same file
-- to get the discharger
#check getSimpTheorems
-- to get the theorems tagged @[simp] from the relevant env extention
#check getSimprocs
-- to do the same for simprocs
#check getSimpCongrTheorems
-- to get theorems from a congr extention I never heared of
-- Sofore we ge the
#check Simp.Context
#check Simp.DischargeWrapper
-- and to get the rest, we call
#check elabSimpArgs

-- The latter parses the information passed to simp in syntax, to produce:
#print ElabSimpArgResult
-- and to add simp theorems to ``, most notably by adding
#print SimpTheorems
/-Which are arguments to simp given by syntax:
      syntax simpPre := "↓"
      syntax simpPost := "↑"
      syntax simpLemma := (simpPre <|> simpPost)? "← "? term
      syntax simpErase := "-" ident
-/
-- Note that the first kind of data mentioned contains
#print SimpTheorem
-- which seems relevant ...

-- At the end of the preparation phase, ↓ are called to tell which hyps & goal to simplify
#check simpLocation
#check dsimpLocation

-- Finally, simp is called with:
#check simpGoal
#check simpAll
#check dsimpGoal



#check simpGoal
-- First simplifies hyps given as location via
#check simp
-- and in case of success carries out the simplifcation in
#check applySimpResult
-- In case a hyp was False, the goal is closed with
#check mkFalseElim
-- Finally the target is simplified (if given as location) via
#check simpTarget
-- Then, the simplified hyps are added to the goal new simplified goal via
#check MVarId.assertHypotheses
-- and we try to clean out unused hyps with
#check MVarId.tryClearMany


#check dsimpGoal
-- acts similarly to ↑, but instead of `simp` and `simpTarget` it uses
#check dsimp
-- It does attempt False.elim on the hyps, but add them to the new goal via:
#check MVarId.replaceLocalDeclDefEq
-- which has nothing to do with the one from `rw`, since types are expected to be defeq
-- Finally, it tries to close the goal with a Eq.refl if it's an eq with defeq sides


-- Roughly speaking, `simpAll` gathers additional simp theorems from the hyps
-- it then simplifies the hyps via
#check simpStep
-- and adds them as potential simp theorems. Finally, it simplifies the target via
#check simpTarget
-- and does so hyp-cleaning afterwards

#check simpTarget
-- boils down to calling `simp` on the main target.
-- If the target was simplfied to `True` (a terminal simp)
-- We assign the goal either
#check True.intro
-- if the target has true without the simp-result requiring a proof,
-- or use ↓ on the proof
#check mkOfEqTrue
-- If it was a non-terminal simp, we use
#check applySimpResultToTarget
-- to simplify the goal, which just calls
#check MVarId.replaceTargetEq
-- that is responsible for `rw at ⊢` or just replaces the goal if the
-- simplified version is simply defeq to the original one.


#check simpStep
-- is just a combo of `simp` and
#check applySimpResult
-- which carries out the simplifaction of a hyp.
-- If the simplifaction has a proof, it simply wraps the proof in a
#check Eq.mp
-- If the simplifyed hyp is `False` we close the goal with `mkFalseElim`
-- If there was no proof (defeq-simplication), then if the type and it simplification
-- aren't euqal, the proof is ↓, which wraps the type (??) in `id`


-- `simp` and `dsimp` are implemented in
#check simpImpl
#check_failure dsimpImpl

-- `simp` doesn't simplify proofs, and calls
#check simpLoop
-- which checks the simp-cache for the expression to be simplified, and uses
-- the simplified expression stored for this key if available
-- It then starts with
#check pre
-- which can either be done, in which case we cache the simplificaiton, or in `visit`
-- where we keep simpliying the expression in ca recursive call to the loop, and
-- connect it to the previous version via:
#check Result.mkEqTrans
-- In a `continue` mode we try reductions via:
#check_failure reduceStep --private, same file
-- If reductions where made, we keep lloping with the `Simp.reduceStep` and `simpLoop` combo
-- Otherwise, we use `Result.mkEqTrans` with
#check Simp.simpStep
-- and keep going with
#check post
-- and finally, at the end of the loop, if progrees was made in the iteration,
-- we call recursively kkep going with `simpLoop`, or we stop.

-- The loop works with a `Result` who's projs have good docs
#check Result.expr
#check Result.proof?
#check Result.cache

-- The `Result.mkEqTrans` used in the loop is just a wrapper around
#check Meta.mkEqTrans
-- which in turn gets ↓ to work
#check Eq.trans



#check pre
#check post
-- attempt to apply simprocs provided by users ; by default they do no simplifications


#check Simp.simpStep
-- Does seem to do most standard simplifying. Most notably the case
#check simpApp
-- Which get the registered simp theorems via
#check SimpCongrTheorems.get
-- where we consider the congr theorems stored under the key that is the constant head of the app
-- The possible rewrite is carried out with
#check trySimpCongrTheorem?
-- Which does that clasic of using `forallMetaTelescopeReducing` on the type of the theorem,
-- then defeqing the lhs of the theorem to the expr, potentially wraps the proof in `propext`.
-- A subtle case is when the congr theorem is about `c x` and the expression is `c x y`.
-- For such a case, the congr theorem is wrapped in
#check Simp.mkCongrFun
#check Simp.mkCongr
-- which are wrappers arround
#check mkCongrFun
#check mkCongr
-- and, returning to `congrArgs`, where further arugements are simplified with calls to `simp`


#check simpLambda
-- simplifies function by simplifying their head, dsimping binding types and considering
-- those that are fit as further possible simp-theorems.
-- It then re-binds the lambdas to the simplified expressions and folds `funext` arround the proof:
#check Result.addLambdas


#check simpForall
-- is similar in spirit, but different in proctice. For, non-dependent binders, we have
#check simpArrow
-- which simplifies the domain and then the body with calls to `simp` and makes
-- a proof with one of
#check Simp.mkImpCongr
#check mkImpCongrCtx
#check mkImpDepCongrCtx
-- depending on the case.
-- For a dempendent domain, we only proceed if we're simplifying a Prop.
-- If the domain is *not* a prop, we only dsimp it, simp the body, and wrap the proof in a
#check mkForallCongr
-- Otherwise, the proof follows from applying
#check forall_prop_domain_congr
-- where the proof of argument `h₂` is actually derived from a call to `simp` !


#check simpProj
-- tries to reduce the expression and if this fails, it tries to simplify the projected
-- expression with `simp` and returns a proof for the projection as follows: it makes an
#check mkEqNDRec
-- With the motive being `fun x => e.i = x.1`, the local occurence being refl, and the
-- proof returned by `simp` as equality argument



-- Can't be bothered to dig through:
#check simpLet
-- The expresions we need to look out for are
#check have_unused_dep'
#check have_unused'
#check have_body_congr_dep'
#check have_val_congr'
#check have_body_congr'
#check have_congr'

#check simpConst
-- carries out unfolds and ι (but is run on const ??)

#check_failure Simp.reduceFVar
-- effectively only unfolds let-bound vars

-- **Note** ; honestly wondering if it'd just be easier to delab by ignoring congr lemmas
-- and their trivial arguements ...

#check_failure reduceStep
-- just carries out reductions and unfolding, depending on configurations
-- and only does a single reduction before proceeding.



#check SimpExtension.getTheorems
-- is the extention for simp theorems, which are made via:
#check mkSimpTheoremFromConst
-- checks if the the theorem should be preprocessed and does so with:
#check_failure preprocess
-- for eqs, possibly wraps in symm, for iff, wraps in propext
-- if its `ne` then check if the other sides is a boolean and use
#check Bool.of_not_eq_true
#check Bool.of_not_eq_false
-- and if the other side isn't a boolean it turns it into a `(a = b) = False` and
-- wraps the proof in a
#check mkEqFalse
#check eq_false
-- Similar things are done for the case of `not eq`
-- For theorems that result in an ∧, we ad two simp theorems, one for each
-- projection by wrapping it in
#check mkProj ``And
-- and if none of the above applied, we change it into a `P = True` via
#check mkEqTrue
#check eq_true
-- This preprocessed result is then added as a auxiliary lemma in
#check mkAuxLemma

-- There is a special case and extentions for congr theorems, which are about equalities
-- which have the same constant head on both sides:
#check mkSimpCongrTheorem
#check getSimpCongrTheorems



#check Mathlib.Tactic.withSimpRWRulesSeq
-- Just repeatedly calls simp ?!?

#check Mathlib.Tactic.simpIntroCore
-- is a mix of simp and intro ... ?


#check getSimpExtension?
-- #eval do let res ← (getSimpExtension? `simp) ; return res.isSome
-- works


def printSimpThms : CoreM Unit := do
   let .some res ← (getSimpExtension? `simp) | panic "Attribut name simp not there ?!?"
   let thms ← res.getTheorems
   for thm in thms.lemmaNames do
      match thm with
      | .decl n => IO.println s!"decl : {n}"
      | .other n => IO.println s!"other : {n}"
      | .stx n _ => IO.println s!"stx : {n}"
      | _ => continue


-- #eval printSimpThms
-- a lot of theorems ; includes private ones


def f : Nat → Nat := sorry

@[simp]
theorem thm_1 (x : Nat) : f (2 * x) = x + 1 := sorry


theorem test_1 (n m : Nat) (P : Nat → Prop) (h : P (n + m + 1)) :
      P (f (2 * (n+m))) := by
      simp only [thm_1]
      exact h

#print test_1


@[simp]
theorem thm_2 (x : Nat) : Even (f (x + 1))  := sorry


theorem test_2 (x : Nat) : Even (f (x + 1)) := by simp

#print test_2
#print thm_2._simp_1

@[simp]
theorem thm_3 (x : Nat) : ¬ Even (f (x - 1))  := sorry


theorem test_3 (x : Nat) : ¬ Even (f (x - 1)) := by simp

#print test_3
#print thm_3._simp_1

-- makes use of
#check not_false_eq_true
-- and eq trans, which we didn't uncover in the above study XD


#print ConvexCone.pointed_iff_not_blunt
#print ConvexCone.disjoint_coe
#print ConvexCone.subset_hull -- non rw
#print ConvexCone.coe_iInf
#print ConvexCone.salient_positive
#print Convex.mem_toCone


#print Set.subset_iInter_iff._simp_1


/-

simpproof
| simprocs ...
| Eq.trans simpproof simpproof
| congrFun simpproof
| congr simpproof simpproof
| propext? (Congrtheorem simpproof*)
| congrArg simpproof
| implies_congr simpproof simpproof
| implies_congr_ctx simpproof (fun _ => simpproof)
| implies_dep_congr_ctx simpproof (fun _ => simpproof)
| forall_prop_domain_congr simpproof (fun _ => simpproof)
| forall_congr (fun _ => simpproof)
| funext (fun _ => simpproof)
| Eq.ndrec refl simpproof
| have_unused_dep' _ (fun _ => simpproof)
| have_unused' _ refl
| have_body_congr_dep' _ (fun _ => simpproof)
| have_val_congr' simpproof
| have_body_congr' (fun _ => simpproof)
| have_congr' simpproof (fun _ => simpproof)
| Eq.refl
| Simptheorem as
| id (Eq.mp simpproof)
      -- couldn't read this, can appear in simp_all
| (eq_false <|> eq_true) ((And.left <|> And.right)? (Eq.mp simpproof))
      -- again, couldn't read this but seems to happen

Simptheorem
| iff_self._simp_1
| x_fst (due to @[simps])
| δ → fun as => Eq.symm? propext? (thm as)
| δ → fun as => (eq_true | eq_false | Bool.of_not_eq_true | Bool.of_not_eq_false) (thm as)
| δ → fun as => (thm as).i.j...
| ...

Congrtheorem
| Set.iInter_congr_Prop
| ...

simpGoal
| True.intro
| of_eq_true simpproof
| Eq.mpr (id simpproof) (_ | simpGoal?)
| False.elim (_ | Eq.mp simpproof (_ | simpproof))
| (_ : ∀ ...) (_ | Eq.mp simpproof (_ | simpproof))+

-/

#check eq_false
#check Eq.mp

#exit

#check Eq.trans
#check congrFun
#check _root_.congr
#check congrArg
#check implies_congr
#check implies_congr_ctx
#check implies_dep_congr_ctx
#check forall_congr
#check forall_prop_domain_congr
#check funext
#check Eq.ndrec

#check have_unused_dep'
#check have_unused'
#check have_body_congr_dep'
#check have_val_congr'
#check have_body_congr'
#check have_congr'


#check of_eq_true
#check Eq.mpr
#check False.elim

-- Todo: Bool stuff

#check iff_self
#check Iff.refl
#check eq_true

#print imp_self._simp_1
#print iff_true_intro
#print iff_of_true
#check exists_prop_congr
#check and_false
#check_failure and_false._simp_1
#check implies_true
#check Set.iInter_congr_Prop
#check Iff.of_eq


@[simps] def foo : ℕ × ℤ := (1, 2)
#check foo_fst
#check foo_snd


#check simpsAttr

def testGetSimps : CoreM Unit := do
      let res := simpsAttr.ext.getState (← getEnv)
      IO.println s!"{res.1}\n"
      IO.println s!"{res.2.toArray}\n"

#eval testGetSimps


#check Bool.of_not_eq_true
#check eq_false
#check Bool.of_not_eq_false


#check getSimpCongrTheorems
#print SimpCongrTheorems
#print SimpCongrTheorem


#check getSimpTheorems
#print SimpTheorems

#check SMap.toList
def testCongrGet := do
      let thms ← Meta.getSimpCongrTheorems
      let inter := thms.lemmas.toList
      for (n,L) in inter do
            IO.println s!"\nKey: {n}"
            for t in L do
            IO.println s!"{t.theoremName}"

#eval testCongrGet


#check getSimpExtension?
#print SimpExtension
#print SimpEntry


def testSimpGet := do
      let thms ← Meta.getSimpTheorems
      let L := thms.lemmaNames.toList
      for t in L do
            match t with
            | .decl n => IO.println s!"{n}"
            | _ => continue


-- #eval testSimpGet
-- takes like 10 sec to load
