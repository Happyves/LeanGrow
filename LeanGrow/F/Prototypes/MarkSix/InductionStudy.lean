

import Mathlib.Tactic

open Lean Meta Mathlib Elab Tactic

-- # todo


#check Lean.mkNoConfusionCoreImp
#check Lean.Meta.mkNoConfusion



-- # Reverting

#check MVarId.revertAll


#check MVarId.revert
#check Meta.collectForwardDeps
#check MetavarContext.MkBinding.collectForwardDeps
#check localDeclDependsOn
#check findLocalDeclDependsOn
#check MetavarContext.revert
#check_failure MetavarContext.MkBinding.elimMVar


/-
Rerverting corresponds to assigning to the current goal, given g1 g2 ... in ltx,
the solution `g? g1 g2 ...`, where g? is a new goal of type `∀ g1 : g1T, ...., oldgoal`

We note that Lean allows to revert more then a single fvar. One then has to consider the dependencies
among the initial fvars to revert, and make sure to consider all dependencies...

The core function to collect dependencies is `MetavarContext.MkBinding.collectForwardDeps`.
It first gos through the array of fvars we want to find dependeies for, and revert, and checks
that they are in independent of prior entries. Dependence is check via either `localDeclDependsOn`
or `findLocalDeclDependsOn`, which basicly look at the type (& value for lets) and check if it contains
any of the previous fvar. Then, we fold over the local context and add fvars to the list of those to be
reverted, by checking dependence to prior ones.

Back in `revert`, after some cleaning, we use `MetavarContext.revert`, which has its main implementation
in `MetavarContext.MkBinding.elimMVar`. It seems to boil down to making a big ∀ in `mkAuxMVarType` with
the reverted types, and replaced by correspoding bvars in initial goal, and adds the fvars back in an
application.

-/

#check induction
-- first implementation

-- gets indices via
#check Meta.getMajorTypeIndices
-- and does some wierd error checking I don't fully understand
-- we also check if dependent elimination is allowed in
#check Meta.RecursorInfo.depElim
--throw error if its false ad the goals depends on it (otherwise, we can consider a constant motive)
-- Then we revret all hyps related to the indices and the fvar being inducted on, of the inductive type via
#check MVarId.revert
-- Then we reIntroduce the inidces and majorPremines (fvar we induct on)
-- Then the recursor application is built in two steps
#check mkRecursorAppPrefix
-- seems to build the recursor and the motive, and apply it to the motive
#check_failure Meta.finalize
-- adds the remaining arguments, and sets new goals?
-- In `` the recursor is built as a constant with levels, to which we add parameters via
#check_failure addRecParams
-- the motive is then built with
#check Meta.mkLambdaFVars

#check mkRecursorAppPrefix


#check evalInduction
-- other implementation

#check mkGeneralizationForbiddenSet
#check getFVarSetToGeneralize
#check ElimApp.mkElimApp
