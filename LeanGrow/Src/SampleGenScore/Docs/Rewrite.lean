

import Mathlib.Tactic


open Lean Elab Tactic Meta


#check Parser.Tactic.rewriteSeq
-- ↑ is the parser
#check evalRewriteSeq
-- ↑ evaluates it via ↓
#check withRWRulesSeq
-- which carries out one rewrite after another, where we exploit the convetion that
-- the rewrite goal is the first goal in the tactic state, even when subgoals caused
-- by the rewrite are created.
-- This part also handles realising constants (ex: `.eq_1` and so on)
-- The rewrite loop carries out:
#check elabRewrite


-- Rewrites are different, based on whether we rewrite the goal or a hyp
-- But in both cases, the rewite is carried out by
#check elabRewrite
-- In the case of ↓
#check rewriteTarget
-- `elabRewrite` is called with the main goal mvar and the main target expr
-- An for ↓
#check rewriteLocalDecl
-- `elabRewrite` is called with the main goal mvar and the type of
-- the fvar in context to be rewritten


#check elabRewrite
-- elaborates the syntax of the rw-thorem we want to use (a name, an fvar, a composite term ...)
-- It then use ↓ to produce the equality proof, using ↑, and the information whether to wrap it
-- in `Eq.symm`
#check MVarId.rewrite
-- Notable fact about ↑ is that it wraps a potential `propext` before a potential `Eq.symm`
-- To build the actual equality the "theorem" gets applied to mvars that my be future goals
-- then we search the letf side of the equ it has as type within the goal via
#check kabstract
-- Finally it uses the motive obained this way with ↓ to get the full equality term
#check congrArg


-- To finish for targets in `rewriteTarget` we use
#check MVarId.replaceTargetEq
-- It will assign the goal mvar with an expression that is an
#check Eq.mpr
-- where α is the type of the previous goal, b is a new goal mvar, and h is a term
-- built from the euqality proof initially derived by `MVarId.rewrite`, but wrapped via
#check mkExpectedPropHint
-- in an application with `id`.

-- In `rewriteLocalDecl` useing the equality proof, we conclude with
#check MVarId.replaceLocalDecl
-- This one make a new term from the old fvar with an
#check Eq.mp
-- It then proceeds in assigning the goal as follows, via `Lean.MVarId.assertAfter`.
-- First all fvars depending on the rewritten one are reverted (ie. create ∀-ed goal,
-- assign to initial one that app of it with the reverted fvars) via
#check MVarId.revertAfter
-- It then carries out a final revert of the rewritten mvar,
-- which is where type issues can arise, via
#check MVarId.assert



theorem test_1 (a b : Nat) (P : Nat → Prop)
  (eq : a = b) (h : P a) : P b := by
    rwa [← eq]

#print test_1


theorem test_2 (a b : Nat) (P : Nat → Prop)
  (eq : a = b) (h : P a) : P b := by
    rwa [eq] at h

#print test_2


set_option linter.unusedVariables false in
theorem test_3 (a b : Nat) (P : Nat → Prop) (M : (x : Nat) → P x → Prop)
  (eq : a = b) (h : P a) (spe : M a h) : P b := by
    rw [eq] at h ; assumption

#print test_3
