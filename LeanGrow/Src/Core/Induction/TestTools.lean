
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Core.Induction.Detection
import LeanGrow.Src.Core.Induction.FunctionalInd
import LeanGrow.Src.Core.Induction.ElimInd
import LeanGrow.Src.Core.Induction.StructuralInd
import LeanGrow.Src.Utils.LeanGrow.TestTools
import LeanGrow.Src.Caching.NonStrucIndunction
import LeanGrow.Src.Data.CTrie.Operations

open Lean Meta



def testGoalInduction (mod : Option Name) : Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array DepCache → Array (FVarId × List FVarId) → MetaM Unit
    | guT, gu, tT, t, lT, l, wsT, ws, ewsT, ews, Ts, depCache, wdeps => do
        let initGoal := Ts[0]!
        let data ← (match mod with | .some mod => buildRecursorCache_core mod | .none => return RecursorCachePickle.emptyNamed `test)
        let ⟨tars,l1,l2⟩ ← detectIndGoal (← getLCtx) (← getLocalInstances) data.funrecu data.elimrecu initGoal
        let rec go (l1 : LocalContext) (l2 : LocalInstances) (msgs : List String) : List TargetType → MetaM String
            | [] => pure (String.join msgs)
            | tar :: tars => do
                match tar with
                | .indu major =>
                    match ← inductiveInductionMain (fun _ => true) 10 depCache l1 l2 42 major initGoal with
                    | ⟨.none,l1,l2⟩ => (go l1 l2 (s!"\nFailed on {tar.pp}\n" :: msgs) tars)
                    | ⟨.some res subgs,l1,l2⟩ => go l1 l2 (s!"\nSuccess with term:\n{← PpExpr res l1 l2}\nType correct {← IsTypeCorrect res l1 l2}\nAnd subgoals :\n{← subgs.mapM (PpExpr · l1 l2)}\n" :: msgs) tars
                | .func fvs recu =>
                    match ← functionalInductionMain (fun _ => true) 10 depCache l1 l2 42 initGoal fvs recu with
                    | ⟨.none,l1,l2⟩ => (go l1 l2 (s!"\nFailed on {tar.pp}\n" :: msgs) tars)
                    | ⟨.some res _,l1,l2⟩ => go l1 l2 (s!"\nSuccess with term:\n{← PpExpr res l1 l2}\n" :: msgs) tars
                | .elim fvs recu =>
                    match ← elimInductionMain (fun _ => true) 10 depCache l1 l2 1 initGoal fvs recu with
                    | ⟨.none,l1,l2⟩ => (go l1 l2 (s!"\nFailed on {tar.pp}\n" :: msgs) tars)
                    | ⟨.some res _,l1,l2⟩ => go l1 l2 (s!"\nSuccess with term:\n{← PpExpr res l1 l2}\n" :: msgs) tars
        let msg ← go l1 l2 [] tars
        IO.println msg

#check 1


/-- Will require to make specific defs where we specialize `hypPos` -/
def testHypInduction (mod : Option Name) (hypPos : Nat) : Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array DepCache → Array (FVarId × List FVarId) → MetaM Unit
    | guT, gu, tT, t, lT, l, wsT, ws, ewsT, ews, Ts, depCache, wdeps => do
        let initGoal := Ts[0]!
        let tarHyp := (gu[hypPos]!).fvarId!
        let data ← (match mod with | .some mod => buildRecursorCache_core mod | .none => return RecursorCachePickle.emptyNamed `test)
        let ⟨tars,l1,l2⟩ ← detectIndHyp (← getLCtx) (← getLocalInstances) data.funrecu data.elimrecu tarHyp
        let rec go (l1 : LocalContext) (l2 : LocalInstances) (msgs : List String) : List TargetType → MetaM String
            | [] => pure (String.join msgs)
            | tar :: tars => do
                match tar with
                | .indu major =>
                    -- Should be the case of ∧, ∨, ∃, ...
                    match ← inductiveInductionMain (fun _ => true) 10 depCache l1 l2 1 major initGoal with
                    | ⟨.none,l1,l2⟩ => (go l1 l2 (s!"\nFailed on {tar.pp}\n" :: msgs) tars)
                    | ⟨.some res subgs,l1,l2⟩ => go l1 l2 (s!"\nSuccess with term:\n{← PpExpr res l1 l2}\nAnd subgoals :\n{← subgs.mapM ppExpr}\n" :: msgs) tars
                | .func fvs recu =>
                    -- *Note* even if the goal doesn't contain any of the fvars of teh function appli,
                    -- the hyp that triggered induction will be reverted as desired, since it in particular
                    -- depends on the fvars being reverted
                    match ← functionalInductionMain (fun _ => true) 10 depCache l1 l2 1 initGoal fvs recu with
                    | ⟨.none,l1,l2⟩ => (go l1 l2 (s!"\nFailed on {tar.pp}\n" :: msgs) tars)
                    | ⟨.some res _,l1,l2⟩ => go l1 l2  (s!"\nSuccess with term:\n{← PpExpr res l1 l2}\n" :: msgs) tars
                | .elim fvs recu =>
                    match ← elimInductionMain (fun _ => true) 10 depCache l1 l2 1 initGoal fvs recu with
                    | ⟨.none,l1,l2⟩ => (go l1 l2 (s!"\nFailed on {tar.pp}\n" :: msgs) tars)
                    | ⟨.some res _,l1,l2⟩ => go l1 l2  (s!"\nSuccess with term:\n{← PpExpr res l1 l2}\n" :: msgs) tars
        let msg ← go l1 l2 [] tars
        IO.println msg
