
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrowBeta.Core.Rewriting.Main
import LeanGrowBeta.Utils.LeanGrow.TestTools
import LeanGrowBeta.Utils.Lean.MetaAPI


open Lean Meta


def findFirstAppli
  (l1 : LocalContext) (l2 : LocalInstances)
  (thm : Name) (within : Expr)
  : MetaM (Prod4 Expr Expr LocalContext LocalInstances) := do
  withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
    let Thm ← mkConstWithFreshMVarLevels thm
    let TT ← inferType Thm
    let (args, _, head) ← forallMetaTelescope TT
    let .some (_,pat,_) := head.eq? | throwError "Not an rw theorem ?!?"
    let ⟨res,l1,l2⟩ ← within.onAllSubtermsCheckExistsMTR l1 l2 (fun e _ l1 l2 => do
      -- dbg_trace s!"[findFirstAppli] pat {← ppExpr pat} vs. e {← ppExpr e}"
      if (← defEqWiMvNoClear pat e l1 l2).isSome
      then
        -- dbg_trace "yes !"
        return ⟨true,l1,l2⟩
      else
        clearMvarAssignments
        return ⟨false,l1,l2⟩
      )
    if !res
    then throwError "Pattern not found ..."
    else
      withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
        let pat ← instantiateMVars pat
        let Thm ← instantiateMVars Thm
        let args ← args.mapM instantiateMVars
        -- we don't even check if there are remaining goals &levels cause this is testing and we're lazy
        return ⟨pat,(mkAppN Thm args),l1,l2⟩


def fixWorker (pat : Expr) (d : Nat) (w : Name) : Expr :=
  pat.onAllSubtermsTR (fun
    | x@(.fvar ⟨.num (.str _ k) i⟩) =>
        if k == "w"
        then
          if i == d
          then .fvar ⟨w⟩
          else x
        else x
    | x => x
    )



partial def findDirs
  (l1 : LocalContext) (l2 : LocalInstances)
  (pat within : Expr) (d : Nat)
  {α : Sort _} (k : rwDirs → LocalContext → LocalInstances → MetaM α ): MetaM α :=
  if pat == within
  then k .yes l1 l2
  else
    match within with
    | .mdata _ e => findDirs l1 l2 pat e d k
    | .app l r =>
      findDirs l1 l2 pat l d <| fun L l1 l2 => do
        findDirs l1 l2 pat r d <| fun R l1 l2 => do
          match L, R with
          | .no, .no => k .no l1 l2
          | _, _ => k (.ap L R) l1 l2
    | .lam _ l r _ =>
      findDirs l1 l2 pat l d <| fun L l1 l2 => do
        let w ← worker d
        let pat := fixWorker pat d w
        let ⟨_,r,l1,l2⟩ ← withFreeing w l r l1 l2
        findDirs l1 l2 pat r (d+1) <| fun R l1 l2 => do
          match L, R with
          | .no, .no => k .no l1 l2
          | _, _ => k (.la L R) l1 l2
    | .forallE _ l r _ =>
      findDirs l1 l2 pat l d <| fun L l1 l2 => do
        let w ← worker d
        let pat := fixWorker pat d w
        let ⟨_,r,l1,l2⟩ ← withFreeing w l r l1 l2
        findDirs l1 l2 pat r (d+1) <| fun R l1 l2 => do
          match L, R with
          | .no, .no => k .no l1 l2
          | _, _ => k (.al L R) l1 l2
    | .letE _ l r z _ =>
      findDirs l1 l2 pat l d <| fun L l1 l2 => do
        findDirs l1 l2 pat r d <| fun R l1 l2 => do
          let w ← worker d
          let pat := fixWorker pat d w
          let ⟨_,z,l1,l2⟩ ← withFreeingLet w l r z l1 l2
          findDirs l1 l2 pat z (d+1) <| fun Z l1 l2 => do
            match L, R with
            | .no, .no => k .no l1 l2
            | _, _ => k (.le L R Z) l1 l2
    | .proj _ _ l =>
      findDirs l1 l2 pat l d <| fun L l1 l2 => do
        match L with
        | .no => k .no l1 l2
        | _ => k (.pro L) l1 l2
    | _ => k .no l1 l2






def testBackRW (thm : Name) : Array Expr → Array Expr → Array Expr → Array Expr → MetaM Unit
  | Gnodes, Unodes, Tnodes, Objs => do
      let depCache ← mkFakeDepCache Gnodes Unodes
      IO.println s!"[testBackRW] built depCache : {repr <| depCache.map (fun l => l.map LocalDecl.fvarId)}"
      let initGoal := Objs[0]!
      let ⟨pat,eqProof,l1,l2⟩ ← findFirstAppli (← getLCtx) (← getLocalInstances) thm initGoal
      IO.println s!"[testBackRW] pat {← ppExpr pat}"
      IO.println s!"[testBackRW] eqProof {← ppExpr eqProof}"
      IO.println s!"[testBackRW] eqProof type {← ppExpr <| ← inferType eqProof}"
      findDirs l1 l2 pat initGoal 0 <| fun dirs l1 l2 => do
        let ⟨proof,l1,l2⟩ ← mainBackRWData (fun _ => true) depCache l1 l2 dirs 42 7 initGoal pat eqProof
        withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
          IO.println s!"[testBackRW] succeeded with proof:\n(Type) {← ppExpr (← inferType proof)}\n(Value) {← ppExpr proof}\n(Correct) {← isTypeCorrect proof}\n(NewGoal) {← ppExpr <| ← (⟨.num (.num `t 42) 7⟩ : FVarId).getType}"
          let hmm := Kernel.check (← getEnv) l1 proof
          match hmm with
          | .ok _ => IO.println "Correct: yes"
          | .error e => IO.println s!"Correct: no\n{proof}" ; logInfo <| e.toMessageData {}


#check 1
#check Kernel.Exception.toMessageData
