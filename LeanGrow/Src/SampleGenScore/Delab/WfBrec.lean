
/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.SampleGenScore.Utils
import LeanGrow.Src.Utils.LeanGrow.Expr

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
      let nh := nh.getLamBody
      let nh := nh.getAppFn'
      let .const h _ := nh | return false
      return h == ``WellFounded.fix
    else
      if s == "brecOn"
      then return true
      else
        if h == ``WellFounded.fix
        then return true
        else return false
  | _ =>
    return false

#check List.brecOn
#check Nat.brecOn
#check isBRecOnRecursor



def delabWfBrec_absBel (e Bel : Expr) (l1 : LocalContext) (l2 : LocalInstances)
  (ini : List FVarId) : MetaM (Prod4 Expr (List FVarId) LocalContext LocalInstances) := do
    let rec getprojB : Expr → Expr
      | .proj _ _ e => getprojB e
      | e => e
    e.onAllSubtermsWiWorkerCpsSkipTravStateTR l1 l2 ini (fun e _ lif l1 l2 => do
      if getprojB e == Bel
      then
        let T ← InferType e l1 l2
        let T := T.headBeta -- cause motive app !
        let dsiambig ← mkFreshId
        let .mk aT ws l1 l2 ← T.abstractWorkersAll l1 l2
        let .mk fv l1 l2 ← WithLocalDecl (dsiambig ++ `AccLift) aT l1 l2
        let rep := mkAppN (.fvar fv) (ws.map Expr.fvar)
        return .mk (.ok rep) (fv :: lif) l1 l2
      else
        return .mk (.ok e) lif l1 l2
      )

#check 1





@[inline]
partial def delabDig_WfBrec_core (inibins : List FVarId)
  (appH : Expr) (appA : Array Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (Prod3 (OptionProd (List Expr) (List FVarId)) LocalContext LocalInstances) := do
  mtracing
  let .const h _ := appH | return .mk .none l1 l2
  mtrace on .zero with s!" head {h}"
  let main_wf := do
    let A := appA[4]!
    mtrace on .zero with s!" wf case with proof arg {← PpExpr A l1 l2}"
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
    let .mk prf acc lif l1 l2 ← consumePSigma l1 l2 inibins A
    mtrace on .zero with s!" after consumePSigma\n lif {← lif.mapM (fun x => do return (x.name, ← ppExpr (← x.GetType l1 l2)))}\n acc {← PpExpr acc l1 l2}\n prf {← PpExpr prf l1 l2}"
    match prf.getAppFn' with
    | .const h _ =>
      if ← isMatcher h
      then
        let .some matin ← getMatcherInfo? h | return .mk .none l1 l2
        let mut nex := []
        let as := prf.getAppArgs
        for i in matin.getAltRange do
          let H := as[i]! -- don't clean unit, as messes with altNumParams
          match H with
          | .lam _ (.const u? _) b _ =>
            if u? == ``Unit
            then nex := b :: nex
            else nex := H :: nex
          | _ =>
            nex := H :: nex
        mtrace on .zero with s!" matcher, cleaned branches {← nex.mapM ppExpr}"
        let .mk _ prfs lif l1 l2 ← nex.foldlM (fun (.mk i prfs lif l1 l2) t => do
          let tk := matin.altNumParams[i]!
          let .mk head bins l1 l2 ← LambdaLetBoundedTelescope t 0 l1 l2 (tk+1)
          let lif := bins.foldl (fun l f => f.fvarId! :: l) lif
          return .mk (i-1) (head :: prfs) lif l1 l2
          ) (Prod5.mk (matin.numAlts - 1) [] lif l1 l2)
        return .mk (.some prfs lif) l1 l2
      else
        mtrace on .zero with s!" not matcher {← PpExpr A l1 l2}\n nlif {← lif.mapM (fun x => do return (x.name, ← ppExpr (← x.GetType l1 l2)))}\n npr {← PpExpr prf l1 l2}"
        return .mk (.some [prf] lif) l1 l2
    | _ =>
      mtrace on .zero with s!" not matcher {← PpExpr A l1 l2}\n nlif {← lif.mapM (fun x => do return (x.name, ← ppExpr (← x.GetType l1 l2)))}\n npr {← PpExpr prf l1 l2}"
        return .mk (.some [prf] lif) l1 l2
  let main_brec := do
    let info ← getFunInfo appH
    let A := appA[info.paramInfo.size - 1]!
    -- we need this because teh motive may be a function, and the brec is then
    -- applied to fiurther args. Also, we assume the "step" to be last arg of brecS
    mtrace on .zero with s!" brec case with proof arg {← PpExpr A l1 l2}"
    let .mk prf bins l1 l2 ← LambdaLetTelescope A 0 l1 l2
    match prf.getAppFn' with
    | .const h _ =>
      if ← isMatcher h
      then
        let .some matin ← getMatcherInfo? h | return .mk .none l1 l2
        let mut nex := []
        mtrace on .zero with s!" matin.getAltRange {matin.getAltRange.toArray}, matin.numAlts {matin.numAlts}"
        let as := prf.getAppArgs
        for i in matin.getAltRange do
          let H := as[i]! -- don't clean unit, as messes with altNumParams
          nex := H :: nex
        mtrace on .zero with s!" matcher, cleaned branches {← nex.mapM ppExpr}"
        let lif := bins.foldl (fun l f => f.fvarId! :: l) []
        let .mk _ prfs lif l1 l2 ← nex.foldlM (fun (.mk i prfs lif l1 l2) t => do
          let tk := matin.altNumParams[i]!
          let .mk head bins l1 l2 ← LambdaLetBoundedTelescope t 0 l1 l2 (tk+1)
          mtrace on .zero with s!" bins {← bins.mapM ppExpr}\nmatin.altNumParams[i]! {tk}"
          let bel := bins[tk]!
          mtrace on .zero with s!" bel {← ppExpr bel}"
          let lif := bins.foldl (fun l f => f.fvarId! :: l) lif
          let .mk npr nlif l1 l2 ← delabWfBrec_absBel head bel l1 l2 lif
          mtrace on .zero with s!" abstracted {← PpExpr npr l1 l2}"
          return .mk (i-1) (npr :: prfs) nlif l1 l2
          ) (Prod5.mk (matin.numAlts - 1) [] lif l1 l2)
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
      let .mk nh bins l1 l2 ← LambdaLetTelescope nh 0 l1 l2
      let na := nh.getAppArgs
      let nh := nh.getAppFn'
      delabDig_WfBrec_core (bins.foldl (fun l e => e.fvarId! :: l) []) nh na l1 l2
    else
      if s == "brecOn"
      then main_brec
      else
        if h == ``WellFounded.fix
        then main_wf
        else return .mk .none l1 l2
  | _ =>
    return .mk .none l1 l2


#check 1


/-
Todo:
- trace
- test
- fix delabdig /digexpr to handle delabs returning mutiple digs

-/
