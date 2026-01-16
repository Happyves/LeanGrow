
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrowBeta.Core.Induction.Format
import LeanGrowBeta.Data.CTrie.Basic


open Lean Meta



inductive TargetType where
| indu (major : Expr)
| func (targets : Array FVarId) (recu : FunRecursorCache)
| elim (target : FVarId) (recu : RecursorCache)
deriving Inhabited, Repr, BEq


def TargetType.pp : TargetType → String
| .indu m => s!"indu {m}"
| .func m r => s!"func {r.name} {repr m}"
| .elim m r => s!"elim {r.name} {repr m}"


def funIndTarget
  (l1 : LocalContext) (l2 : LocalInstances)
  (recus : CTrie FunRecursorCache) (e : Expr) : MetaM (Option TargetType) :=
  match e with
  | .app .. => do
      let (h,args) := (← WhnfAtMostI e l1 l2).getAppFnArgs
      mtrace on .zero with s!"[funIndTarget] looking at application {← ppExpr e}"
      match recus.find? h.toString.toUTF8 with
      | .none =>
          mtrace on .one with s!"[funIndTarget] no fun-induct found"
          return .none
      | .some recu =>
          if recu.argNum > args.size
          then
            mtrace on .one with s!"[funIndTarget] partial application"
            return .none
          else
            let as := recu.targets.foldl (fun out i => out.push args[i]!) #[]
            if as.any (fun
              | .fvar fid => fid.isWorker || fid.isUnode || fid.isTnode
              | _ => true
              )
            then
              return .none
            else
              mtrace on .zero with s!"[funIndTarget] success"
              return .some <| .func (as.map Expr.fvarId!) recu
  | _ => return .none


def TargetTypeBlackList : CTrie Unit := (CTrie.ofListKeys [`Eq])


def detectIndHyp
  (l1 : LocalContext) (l2 : LocalInstances)
  (funrecus : CTrie FunRecursorCache) (elimrecus : CTrie (List RecursorCache))
  (hyp : FVarId) : MetaM (Prod3 (List TargetType) LocalContext LocalInstances) :=
  trace set TracingFlags.none in do
  let T ← hyp.GetType l1 l2
  let T ← WhnfAtMostI T l1 l2
  let Res@⟨fs,l1,l2⟩ ← T.onAllSubtermsFoldM l1 l2 [] (fun e _ _ l1 l2 R =>  do
    match ← funIndTarget l1 l2 funrecus e with
    | .none => return ⟨R,l1,l2⟩
    | .some new => return ⟨R.insert new,l1,l2⟩)
  mtrace on .zero with s!"[detectIndHyp] functional induction targets {fs.map TargetType.pp}"
  mtrace on .one with s!"[detectIndHyp] sanity {← ppExpr T}"
  if ← IsProp T l1 l2
  then
    mtrace on .zero with s!"[detectIndHyp] hyp is a prop"
    let .const n _ := T.getAppFn | return Res
    let key := n.toString.toUTF8
    match TargetTypeBlackList.find? key with
    | .none =>
        let eliminators : List TargetType :=
          match elimrecus.find? key with
          | .none => fs
          | .some recu =>
              let here := (recu.map (fun R => .elim hyp R))
              trace on .zero with s!"[detectIndHyp] eliminator induction targets {here.map TargetType.pp}" in
              here ++ fs
        match (← getEnv).find? n with
        | .some info =>
            match info with
            | .inductInfo .. =>
              mtrace on .zero with s!"[detectIndHyp] structural induction target"
              return ⟨(.indu (.fvar hyp)) :: eliminators, l1,l2⟩
            | .quotInfo .. =>
              mtrace on .zero with s!"[detectIndHyp] quotient induction target"
              return ⟨(.elim hyp QuotIndRecursorCacheManual) :: eliminators, l1,l2⟩
            | _ =>
              return ⟨eliminators, l1,l2⟩
        | _ =>
            return ⟨eliminators, l1,l2⟩
    | .some .. =>
        return Res
  else
    return Res


partial def detectIndGoal
  (l1 : LocalContext) (l2 : LocalInstances)
  (funrecus : CTrie FunRecursorCache) (elimrecus : CTrie (List RecursorCache))
  (goal : Expr) : MetaM (Prod3 (List TargetType) LocalContext LocalInstances) :=
  trace set TracingFlags.none in do
  let main (sub : Expr) (l1 : LocalContext) (l2 : LocalInstances) (sofar : List TargetType) : MetaM (Prod3 (List TargetType) LocalContext LocalInstances) := do
    mtrace on .one with s!"[detectIndGoal] looking at {← ppExpr sub}"
    let fs :=
      match ← funIndTarget l1 l2 funrecus sub with
      | .none =>
          sofar
      | .some x =>
          trace on .zero with s!"[detectIndGoal] functional induction target {x.pp}" in
          sofar.insert x
    match sub with
    | .fvar fid =>
        if fid.isWorker || fid.isUnode || fid.isTnode
        then return ⟨sofar, l1,l2⟩
        else
          let T ← WhnfAtMostI (← fid.GetType l1 l2) l1 l2
          let .const n _ := T.getAppFn | return ⟨fs, l1,l2⟩
          let key := n.toString.toUTF8
          match TargetTypeBlackList.find? key with
          | .none =>
              let eliminators : List TargetType :=
                match elimrecus.find? key with
                | .none => fs
                | .some recu => recu.foldl (fun R r =>
                      trace on .zero with s!"[detectIndGoal] eliminator induction targets {(TargetType.elim fid r).pp}" in
                      R.insert (.elim fid r)) fs
              match (← getEnv).find? n with
              | .some info =>
                  match info with
                  | .inductInfo .. =>
                    mtrace on .zero with s!"[detectIndGoal] structural induction target"
                    return ⟨eliminators.insert (.indu (.fvar fid)), l1,l2⟩
                  | .quotInfo .. =>
                    mtrace on .zero with s!"[detectIndGoal] structural induction target"
                    return ⟨eliminators.insert (.elim fid QuotIndRecursorCacheManual), l1,l2⟩
                  | _ =>
                    return ⟨eliminators, l1,l2⟩
              | _ =>
                  return ⟨eliminators, l1,l2⟩
          | .some .. =>
              return ⟨fs, l1,l2⟩
    | _ =>
        return ⟨fs, l1,l2⟩
  goal.onAllSubtermsFoldNoPartialM l1 l2 [] (fun x _ _ w l1 l2 => main x l1 l2 w)
