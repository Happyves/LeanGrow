
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrowBeta.Core.Induction.Detection
import LeanGrowBeta.Core.Induction.FunctionalInd
import LeanGrowBeta.Core.Induction.ElimInd
import LeanGrowBeta.Core.Induction.StructuralInd
import LeanGrowBeta.Utils.LeanGrow.TestTools
import LeanGrowBeta.Caching.NonStrucIndunction
import LeanGrowBeta.Data.CTrie.Operations

open Lean Meta



unsafe def testGoalInduction (cacheName : Name) : Array Expr → Array Expr → Array Expr → Array Expr → MetaM Unit
  | Gnodes, Unodes, _, Objs => do
      let depCache ← mkFakeDepCache Gnodes Unodes
      IO.println "[testGoalInduction] built depCache"
      let initGoal := Objs[0]!
      let ctx ← read
      let st ← get
      withRecursorCacheWith ctx st cacheName <| fun data => do
        let ⟨tars,l1,l2⟩ ← detectIndGoal (← getLCtx) (← getLocalInstances) data.funrecu data.elimrecu initGoal
        let rec go (l1 : LocalContext) (l2 : LocalInstances) (msgs : List String) : List TargetType → MetaM String
            | [] => pure (String.join msgs)
            | tar :: tars => do
                match tar with
                | .indu major =>
                    match ← inductiveInductionData (fun _ => true) depCache #[] 10 l1 l2 1 major initGoal with
                    | ⟨.none,l1,l2⟩ => (go l1 l2 (s!"\nFailed on {tar.pp}\n" :: msgs) tars)
                    | ⟨.some res subgs,l1,l2⟩ => go l1 l2 (s!"\nSuccess with term:\n{← PpExpr res l1 l2}\nType correct {← IsTypeCorrect res l1 l2}\nAnd subgoals :\n{← subgs.mapM (PpExpr · l1 l2)}\n" :: msgs) tars
                | .func fvs recu =>
                    match ← functionalInductionData (fun _ => true) depCache  #[] 10 l1 l2 1 initGoal fvs recu with
                    | ⟨.none,l1,l2⟩ => (go l1 l2 (s!"\nFailed on {tar.pp}\n" :: msgs) tars)
                    | ⟨.some res _,l1,l2⟩ => go l1 l2 (s!"\nSuccess with term:\n{← PpExpr res l1 l2}\n" :: msgs) tars
                | .elim fvs recu =>
                    match ← elimInductionData (fun _ => true) depCache  #[] 10 l1 l2 1 initGoal fvs recu with
                    | ⟨.none,l1,l2⟩ => (go l1 l2 (s!"\nFailed on {tar.pp}\n" :: msgs) tars)
                    | ⟨.some res _,l1,l2⟩ => go l1 l2 (s!"\nSuccess with term:\n{← PpExpr res l1 l2}\n" :: msgs) tars
        go l1 l2 [] tars



/-- Will require to make specific defs where we specialize `hypPos` -/
unsafe def testHypInduction (cacheName : Name) (hypPos : Nat) : Array Expr → Array Expr → Array Expr → Array Expr → MetaM Unit
  | Gnodes, Unodes, _, Objs => do
      let tot := Gnodes ++ Unodes
      let depCache ← mkFakeDepCache Gnodes Unodes
      let initGoal := Objs[0]!
      let tarHyp := (tot[hypPos]!).fvarId!
      let ctx ← read
      let st ← get
      withRecursorCacheWith ctx st cacheName <| fun data => do
        let ⟨tars,l1,l2⟩ ← detectIndHyp (← getLCtx) (← getLocalInstances) data.funrecu data.elimrecu tarHyp
        let rec go (l1 : LocalContext) (l2 : LocalInstances) (msgs : List String) : List TargetType → MetaM String
            | [] => pure (String.join msgs)
            | tar :: tars => do
                match tar with
                | .indu major =>
                    -- Should be the case of ∧, ∨, ∃, ...
                    match ← inductiveInductionData (fun _ => true) depCache  #[] 10 l1 l2 1 major initGoal with
                    | ⟨.none,l1,l2⟩ => (go l1 l2 (s!"\nFailed on {tar.pp}\n" :: msgs) tars)
                    | ⟨.some res subgs,l1,l2⟩ => go l1 l2 (s!"\nSuccess with term:\n{← PpExpr res l1 l2}\nAnd subgoals :\n{← subgs.mapM ppExpr}\n" :: msgs) tars
                | .func fvs recu =>
                    -- *Note* even if the goal doesn't contain any of the fvars of teh function appli,
                    -- the hyp that triggered induction will be reverted as desired, since it in particular
                    -- depends on the fvars being reverted
                    match ← functionalInductionData (fun _ => true) depCache  #[] 10 l1 l2 1 initGoal fvs recu with
                    | ⟨.none,l1,l2⟩ => (go l1 l2 (s!"\nFailed on {tar.pp}\n" :: msgs) tars)
                    | ⟨.some res _,l1,l2⟩ => go l1 l2  (s!"\nSuccess with term:\n{← PpExpr res l1 l2}\n" :: msgs) tars
                | .elim fvs recu =>
                    match ← elimInductionData (fun _ => true) depCache  #[] 10 l1 l2 1 initGoal fvs recu with
                    | ⟨.none,l1,l2⟩ => (go l1 l2 (s!"\nFailed on {tar.pp}\n" :: msgs) tars)
                    | ⟨.some res _,l1,l2⟩ => go l1 l2  (s!"\nSuccess with term:\n{← PpExpr res l1 l2}\n" :: msgs) tars
        go l1 l2 [] tars



unsafe def testGoalInductionMulti (cacheNames : Array Name) : Array Expr → Array Expr → Array Expr → Array Expr → MetaM Unit
  | Gnodes, Unodes, _, Objs => do
      let depCache ← mkFakeDepCache Gnodes Unodes
      IO.println "[testGoalInduction] built depCache"
      let initGoal := Objs[0]!
      let ctx ← read
      let st ← get
      withRecursorCacheWithMulti ctx st cacheNames <| fun datas => do
        let mut fT : CTrie FunRecursorCache := {}
        let mut eT : CTrie (List RecursorCache) := {}
        for d in datas do
            fT := fT.merge (fun x _ => x) d.funrecu
            eT := CTrie.merge (fun x y => (x ++ y)
                ) eT d.elimrecu
        let ⟨tars,l1,l2⟩ ← detectIndGoal (← getLCtx) (← getLocalInstances) fT eT initGoal
        let rec go (l1 : LocalContext) (l2 : LocalInstances) (msgs : List String) : List TargetType → MetaM String
            | [] => pure (String.join msgs)
            | tar :: tars => do
                match tar with
                | .indu major =>
                    match ← inductiveInductionData (fun _ => true) depCache  #[] 10 l1 l2 1 major initGoal with
                    | ⟨.none,l1,l2⟩ => (go l1 l2 (s!"\nFailed on {tar.pp}\n" :: msgs) tars)
                    | ⟨.some res subgs,l1,l2⟩ => go l1 l2 (s!"\nSuccess with term:\n{← PpExpr res l1 l2}\nAnd subgoals :\n{← subgs.mapM ppExpr}\n" :: msgs) tars
                | .func fvs recu =>
                    match ← functionalInductionData (fun _ => true) depCache  #[] 10 l1 l2 1 initGoal fvs recu with
                    | ⟨.none,l1,l2⟩ => (go l1 l2 (s!"\nFailed on {tar.pp}\n" :: msgs) tars)
                    | ⟨.some res _,l1,l2⟩ => go l1 l2  (s!"\nSuccess with term:\n{← PpExpr res l1 l2}\n" :: msgs) tars
                | .elim fvs recu =>
                    match ← elimInductionData (fun _ => true) depCache  #[] 10 l1 l2 1 initGoal fvs recu with
                    | ⟨.none,l1,l2⟩ => (go l1 l2 (s!"\nFailed on {tar.pp}\n" :: msgs) tars)
                    | ⟨.some res _,l1,l2⟩ => go l1 l2 (s!"\nSuccess with term:\n{← PpExpr res l1 l2}\n" :: msgs) tars
        go l1 l2 [] tars
