
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Core.Rewriting.Main
import LeanGrow.Src.Utils.LeanGrow.TestTools
import LeanGrow.Src.Utils.Lean.MetaAPI


open Lean Meta


def findFirstAppli
  (l1 : LocalContext) (l2 : LocalInstances)
  (thm : Name) (within : Expr)
  : MetaM (Prod5 Nat Expr Expr LocalContext LocalInstances) := do
  withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
    let Thm ← mkConstWithFreshMVarLevels thm
    let TT ← inferType Thm
    let (args, _, head) ← forallMetaTelescope TT
    let .some (_,pat,_) := head.eq? | throwError "Not an rw theorem ?!?"
    let ⟨res,l1,l2⟩ ← within.onAllSubtermsFoldMTR l1 l2 (false,0) (fun e d _ l1 l2 st@(f?,_) => do
      -- dbg_trace s!"[findFirstAppli] pat {← ppExpr pat} vs. e {← ppExpr e}"
      if f?
      then return ⟨st,l1,l2⟩
      if (← defEqWiMvNoClear pat e l1 l2).isSome
      then
        -- dbg_trace "yes !"
        return ⟨(true,d),l1,l2⟩
      else
        clearMvarAssignments
        return ⟨st,l1,l2⟩
      )
    if !res.1
    then throwError "Pattern not found ..."
    else
      withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
        let pat ← instantiateMVars pat
        let Thm ← instantiateMVars Thm
        let args ← args.mapM instantiateMVars
        -- we don't even check if there are remaining goals &levels cause this is testing and we're lazy
        return ⟨res.2,pat,(mkAppN Thm args),l1,l2⟩



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



#check 1



def testBackRW_sandBox_noSub (thm : Name) : Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array DepCache → Array (FVarId × List FVarId) → MetaM Unit
  | guT, gu, tT, t, lT, l, wsT, ws, ewsT, ews, Ts, deps, wdeps => do
      IO.println s!"[testBackRW] built depCache : {repr <| deps.mapIdx Prod.mk}"
      let initGoal ← withTransparency .reducible <| reduce (skipTypes := false) Ts[0]!
      let ⟨_,pat,eqProof,l1,l2⟩ ← findFirstAppli (← getLCtx) (← getLocalInstances) thm initGoal
      IO.println s!"[testBackRW] pat {← ppExpr pat}"
      IO.println s!"[testBackRW] eqProof {← ppExpr eqProof}"
      IO.println s!"[testBackRW] eqProof type {← ppExpr <| ← inferType eqProof}"
      findDirs l1 l2 pat initGoal 0 <| fun dirs l1 l2 => do
        -- let Prod3.mk ws l1 l2 ← (do
        --   match ifSubgoalsThenAllWs with
        --   | .none =>
        let r1 ← eqProof.getWorkerIndsTrans l1 l2
        let .mk w2 l1 l2 ← pat.getWorkerIndsTrans r1.2 r1.3
        let ws := (List.orderedUnion r1.1.toList w2.toList)
          -- | .some wLen =>
          --   return Prod3.mk (List.range wLen) l1 l2
          -- )
        let ⟨proof,l1,l2⟩ ← mainBackRW (fun _ => true) deps 10 l1 l2 dirs 42 7 initGoal pat eqProof ws
        match proof with
        | .none => IO.println "[testBackRW] Invalid rewrite"
        | .some proof =>
          withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
            IO.println s!"[testBackRW] succeeded with proof:\n(Type) {← ppExpr (← inferType proof)}\n(Value) {← ppExpr proof}\n(Correct) {← isTypeCorrect proof}\n(NewGoal) {← ppExpr <| ← (⟨.num (.num `t 42) 7⟩ : FVarId).getType}"
            let hmm := Kernel.check (← getEnv) l1 proof
            match hmm with
            | .ok _ => IO.println "Correct: yes"
            | .error e => IO.println s!"Correct: no\n{proof}" ; logInfo <| e.toMessageData {}


#check 1

def testBackRW_sandBox_wiSub (thm : Name) : Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array DepCache → Array (FVarId × List FVarId) → MetaM Unit
  | guT, gu, tT, t, lT, l, wsT, ws, ewsT, ews, Ts, deps, wdeps => do
      IO.println s!"[testBackRW] built depCache : {repr <| deps.mapIdx Prod.mk}"
      let initGoal ← withTransparency .reducible <| reduce (skipTypes := false) Ts[0]!
      let ⟨D,pat,eqProof,l1,l2⟩ ← findFirstAppli (← getLCtx) (← getLocalInstances) thm initGoal
      IO.println s!"[testBackRW] pat {← ppExpr pat}"
      IO.println s!"[testBackRW] eqProof {← ppExpr eqProof}"
      IO.println s!"[testBackRW] eqProof type {← ppExpr <| ← inferType eqProof}"
      findDirs l1 l2 pat initGoal 0 <| fun dirs l1 l2 => do
        let ⟨proof,l1,l2⟩ ← mainBackRW (fun _ => true) deps 10 l1 l2 dirs 42 7 initGoal pat eqProof ((List.range D) )
        match proof with
        | .none => IO.println "[testBackRW] Invalid rewrite"
        | .some proof =>
          withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
            IO.println s!"[testBackRW] succeeded with proof:\n(Type) {← ppExpr (← inferType proof)}\n(Value) {← ppExpr proof}\n(Correct) {← isTypeCorrect proof}\n(NewGoal) {← ppExpr <| ← (⟨.num (.num `t 42) 7⟩ : FVarId).getType}"
            let hmm := Kernel.check (← getEnv) l1 proof
            match hmm with
            | .ok _ => IO.println "Correct: yes"
            | .error e => IO.println s!"Correct: no\n{proof}" ; logInfo <| e.toMessageData {}


#check 1


def testForwRW_sandBox (thm : Name) : Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array DepCache → Array (FVarId × List FVarId) → MetaM Unit
  | guT, gu, tT, t, lT, l, wsT, ws, ewsT, ews, Ts, deps, wdeps => do
      IO.println s!"[testForwRW] built depCache : {repr <| deps.mapIdx Prod.mk}"
      let initGoal ← withTransparency .reducible <| reduce (skipTypes := false) Ts[0]!
      withLocalDecl `testing .default initGoal <| fun fv => do
        let ⟨_,pat,eqProof,l1,l2⟩ ← findFirstAppli (← getLCtx) (← getLocalInstances) thm initGoal
        IO.println s!"[testForwRW] pat {← ppExpr pat}"
        IO.println s!"[testForwRW] eqProof {← ppExpr eqProof}"
        IO.println s!"[testForwRW] eqProof type {← ppExpr <| ← inferType eqProof}"
        findDirs l1 l2 pat initGoal 0 <| fun dirs l1 l2 => do
          let ⟨proof,l1,l2⟩ ← mainForwRW (fun _ => true) deps 10 l1 l2 dirs fv initGoal pat eqProof
          match proof with
          | .none => IO.println "[testForwRW] Invalid rewrite"
          | .some proof =>
            withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
              IO.println s!"[testForwRW] succeeded with proof:\n(Type) {← ppExpr (← inferType proof)}\n(Value) {← ppExpr proof}\n(Correct) {← isTypeCorrect proof}"
              let hmm := Kernel.check (← getEnv) l1 proof
              match hmm with
              | .ok _ => IO.println "Correct: yes"
              | .error e => IO.println s!"Correct: no\n{proof}" ; logInfo <| e.toMessageData {}


#check 1
