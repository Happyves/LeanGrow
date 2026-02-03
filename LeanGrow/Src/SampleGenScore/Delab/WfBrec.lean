
/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.SampleGenScore.Utils
import LeanGrow.Src.Utils.Lean.Expr.Basic

open Lean Meta


@[inline]
partial def delabSample_WfBrec_core (appH : Expr)
  : MetaM Bool := do
  let .const h _ := appH | return false
  match h with
  | .str _ s =>
    if s == "_unary"
    then
      let .some info := (← getEnv).find? h | throwError s!"[delabSample_WfBrec_core] unknonw var {h}"
      let val := info.value!
      let nh := val.getAppFn'
      delabSample_WfBrec_core nh
    else
      if s == "brecOn"
      then return true
      else return false
  | _ =>
    if h == ``WellFounded.fix
    then return true
    else return false

#check List.brecOn
#check Nat.brecOn
#check isBRecOnRecursor

#check Expr.onAllSubtermsWiWorkerCpsSkipTravStateTR

def delabWfBrec_absAcc (e Acc : Expr) (l1 : LocalContext) (l2 : LocalInstances)
  (ini : List FVarId) : MetaM (Prod4 Expr (List FVarId) LocalContext LocalInstances) := do
    e.onAllSubtermsWiWorkerCpsSkipTravStateTR l1 l2 ini (fun e _ lif l1 l2 => do
      if e.getAppFn' == Acc
      then
        let T ← InferType e l1 l2 -- is not expected to have workers ...
        let T := T.headBeta -- ? cause motive app ?
        let dsiambig ← mkFreshId
        let .mk fv l1 l2 ← WithLocalDecl (dsiambig ++ `AccLift) T l1 l2
        return .mk (.ok (.fvar fv)) (fv :: lif) l1 l2
      else
        return .mk (.ok e) lif l1 l2
      )

def delabWfBrec_absBel (e Bel : Expr) (l1 : LocalContext) (l2 : LocalInstances)
  (ini : List FVarId) : MetaM (Prod4 Expr (List FVarId) LocalContext LocalInstances) := do
    let rec getprojB : Expr → Expr
      | .proj _ _ e => getprojB e
      | e => e
    e.onAllSubtermsWiWorkerCpsSkipTravStateTR l1 l2 ini (fun e _ lif l1 l2 => do
      if getprojB e == Bel
      then
        let T ← InferType e l1 l2 -- is not expected to have workers ...
        let T := T.headBeta -- cause motive app !
        let dsiambig ← mkFreshId
        let .mk fv l1 l2 ← WithLocalDecl (dsiambig ++ `AccLift) T l1 l2
        return .mk (.ok (.fvar fv)) (fv :: lif) l1 l2
      else
        return .mk (.ok e) lif l1 l2
      )


@[inline]
partial def delabDig_WfBrec_core (appH : Expr) (appA : Array Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (Prod3 (OptionProd (List Expr) (List FVarId)) LocalContext LocalInstances) := do
  let .const h _ := appH | return .mk .none l1 l2
  let main_wf := do
    let A := appA[4]!
    let rec consumePSigma (l1 : LocalContext) (l2 : LocalInstances) (lif : List FVarId)
      (e : Expr) : MetaM (Prod5 Expr Expr (List FVarId) LocalContext LocalInstances) := do
        let .mk head bins l1 l2 ← LambdaLetTelescope e 0 l1 l2
        let lif := bins.foldl (fun l f => f.fvarId! :: l) lif
        match head.getAppFn' with
        | .const n _ =>
          if n == ``PSigma.casesOn
          then consumePSigma l1 l2 lif (head.getArg! 4).getAppFn'
          else return .mk head bins[bins.size-1]! lif l1 l2
        | _ =>
          return .mk head bins[bins.size-1]! lif l1 l2
    let .mk prf acc lif l1 l2 ← consumePSigma l1 l2 [] A
    match prf.getAppFn' with
    | .const h _ =>
      if ← isMatcher h
      then
        let .some matin ← getMatcherInfo? h | return .mk .none l1 l2
        let mut nex := []
        for i in matin.getAltRange do
          let H := appA[i]!
          match H with
          | .lam _ (.const u? _) b _ =>
            if u? == ``Unit
            then nex := b :: nex
            else nex := H :: nex
          | _ =>
            nex := H :: nex
        let .mk prfs lif l1 l2 ← nex.foldlM (fun (.mk prfs lif l1 l2) t => do
          let .mk head bins l1 l2 ← LambdaLetTelescope t 0 l1 l2
          let acc := bins[matin.numDiscrs]! -- assumed, todo : check
          let lif := bins.foldl (fun l f => f.fvarId! :: l) lif
          let .mk npr nlif l1 l2 ← delabWfBrec_absAcc head acc l1 l2 lif
          return .mk (npr :: prfs) nlif l1 l2
          ) (Prod4.mk [] lif l1 l2)
        return .mk (.some prfs lif) l1 l2
      else
        let .mk npr nlif l1 l2 ← delabWfBrec_absAcc prf acc l1 l2 lif
        return .mk (.some [npr] nlif) l1 l2
    | _ =>
      let .mk npr nlif l1 l2 ← delabWfBrec_absAcc prf acc l1 l2 lif
      return .mk (.some [npr] nlif) l1 l2
  let main_brec := do
    let info ← getFunInfo appH
    let A := appA[info.paramInfo.size - 1]!
    -- we need this because teh motive may be a function, and the brec is then
    -- applied to fiurther args. Also, we assume the "step" to be last arg of brecS
    let .mk prf bins l1 l2 ← LambdaLetTelescope A 0 l1 l2
    match prf.getAppFn' with
    | .const h _ =>
      if ← isMatcher h
      then
        let .some matin ← getMatcherInfo? h | return .mk .none l1 l2
        let mut nex := []
        for i in matin.getAltRange do
          let H := appA[i]!
          match H with
          | .lam _ (.const u? _) b _ =>
            if u? == ``Unit
            then nex := b :: nex
            else nex := H :: nex
          | _ =>
            nex := H :: nex
        let lif := bins.foldl (fun l f => f.fvarId! :: l) []
        let .mk prfs lif l1 l2 ← nex.foldlM (fun (.mk prfs lif l1 l2) t => do
          let .mk head bins l1 l2 ← LambdaLetTelescope t 0 l1 l2
          let bel := bins[matin.numDiscrs]! -- assumed, todo : check
          let lif := bins.foldl (fun l f => f.fvarId! :: l) lif
          let .mk npr nlif l1 l2 ← delabWfBrec_absBel head bel l1 l2 lif
          return .mk (npr :: prfs) nlif l1 l2
          ) (Prod4.mk [] lif l1 l2)
        return .mk (.some prfs lif) l1 l2
      else
        return .mk .none l1 l2
    | _ =>
      return .mk .none l1 l2
  match h with
  | .str _ s =>
    if s == "_unary"
    then
      let .some info := (← getEnv).find? h | throwError s!"[delabSample_WfBrec_core] unknonw var {h}"
      let val := info.value!
      let nh := val.getAppFn'
      let na := val.getAppArgs
      delabDig_WfBrec_core nh na l1 l2
    else
      if s == "brecOn"
      then main_brec
      else return .mk .none l1 l2
  | _ =>
    if h == ``WellFounded.fix
    then main_wf
    else return .mk .none l1 l2


#check 1


/-
Todo:
- trace
- test
- fix delabdig /digexpr to handle delabs returning mutiple digs

-/
