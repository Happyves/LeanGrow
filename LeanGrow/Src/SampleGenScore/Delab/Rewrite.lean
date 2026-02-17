
/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.SampleGenScore.Utils

open Lean Meta

partial def consumeSymmPropext (e : Expr) : Expr :=
  let (h,as) := e.getAppFnArgs
  if h == ``Eq.symm
  then
    consumeSymmPropext as[3]!
  else
    if h == `propext
    then
      consumeSymmPropext as[2]!
    else
      e

@[inline]
def delabRW_core (h : Name) (as : Array Expr) : OptionProd Expr Expr :=
  if h == ``Eq.mpr
  then
    let eq := as[2]!
    let rhs := as[3]!
    let (h,as) := eq.getAppFnArgs
    if h == ``id
    then
      let (h,as) := as[1]!.getAppFnArgs
      if h == ``congrArg
      then
        let main := consumeSymmPropext as[5]!
        .some main rhs
      else
        .none
    else
      .none
  else
    if h == ``Eq.mp
    then
      let eq := as[2]!
      let rhs := as[3]!
      let (h,as) := eq.getAppFnArgs
      if h == ``congrArg
      then
        let main := consumeSymmPropext as[5]!
        .some main rhs
      else
        .none
    else
      .none


partial def Lean.Expr.pseudoConstSpe (l1 : LocalContext) (l2 : LocalInstances) : Expr → MetaM (Option Name)
  | .lam .. | .forallE .. => return .none
  | .letE _ _ V B _ => (B.instantiate1 V).pseudoConst l1 l2
  | e@(.app ..) => do
      match ← e.getAppFn.pseudoConstSpe l1 l2 with
      | R@(.some _) =>
        let as ← e.getRelevantArgsBack l1 l2
        if ← as.allM (fun a =>
          if a.isAtomic
          then return true
          else return !(← IsProof a l1 l2)
          )
        then return R
        else return .none
      | R =>
        return R
  | .proj _ _ e | .mdata _ e => e.pseudoConst l1 l2
  | .const n _ => return .some n
  | _ => return .none



@[inline]
partial def delabSample_Rewrite_core (appH : Expr) (appA : Array Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (Prod5 (List FVarId) (Option (List Expr)) (Option Expr) LocalContext LocalInstances) := do
  mtracing
  match appH with
  | .const h _ =>
      match delabRW_core h appA with
      | .none =>
          return .mk [] .none .none l1 l2
      | .some main ini =>
          mtrace on .zero with s!" main {← ppExpr main}"
          mtrace on .one with s!" ini {← ppExpr ini}"
          if (← main.pseudoConstSpe l1 l2).isSome
          then -- case of standard rw
            let appH := main.getAppFn
            let appA := main.getAppArgs
            let rarg ← appH.withRelevantArgsBack l1 l2 appA [] (fun x xs => return x :: xs)
            return .mk [] (← (ini :: rarg).filterM (fun
                | .fvar fvid => do
                  match ← fvid.GetDecl l1 l2 with
                  | .ldecl .. => return true
                  | _ => return false
                | x => return !x.isAtomic)
                ) (.some main) l1 l2
          else -- funky stuff like rw[(show _ from by _)]
            let disambig ← mkFreshId
            let .mk fv l1 l2 ← WithLocalDecl (`funkyRwLift ++ disambig) (← InferType main l1 l2) l1 l2
            return (if ini.isAtomic then .mk [fv] (.some []) .none l1 l2 else .mk [fv] [ini]  .none l1 l2)
  | _ =>
      return .mk [] .none .none l1 l2


@[inline]
partial def delabDig_Rewrite_core (appH : Expr) (appA : Array Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (Option (List Expr)) := do
  mtracing
  match appH with
  | .const h _ =>
      match delabRW_core h appA with
      | .none =>
          return .none
      | .some main ini =>
          mtrace on .zero with s!" main {← ppExpr main}"
          mtrace on .one with s!" ini {← ppExpr ini}"
          -- let appH := main.getAppFn
          -- let appA := main.getAppArgs
          -- if ← appH.isPseudoAtomic l1 l2
          -- then -- case of standard rw
          --   let rarg ← appH.withRelevantArgsBack l1 l2 appA [] (fun x xs => return x :: xs)
          --   return (ini :: rarg).filter (fun x => !x.isAtomic)
          -- else -- funky stuff like rw[(show _ from by _)]
          return (if ini.isAtomic then [main] else [main,ini])
  | _ =>
      return .none


#check 1


@[inline]
partial def delabSample_Rewrite_topBack
  (conjable : CTrie (List Nat))
  (appH : Expr) (appA : Array Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (Option SampleData) := do
  mtracing
  match appH with
  | .const h _ =>
      match delabRW_core h appA with
      | .none =>
          return .none
      | .some main _ =>
          mtrace on .zero with s!" main {← ppExpr main}"
          match ← main.pseudoConstSpe l1 l2 with
          -- needed because rw-thm could have been an inlined have that started as a thm appli
          | .some n => -- case of standard rw
              match conjable.find? n.toString.toUTF8 with
              | .none =>
                return .some <| .thm n
              | .some poses =>
                let cjs := poses.foldl (fun A p => A.push appA[p]!) #[]
                return .some <| .thmC n cjs
          | _ => -- funky stuff like rw[(show _ from by _)]
            return .some <| .none
  | _ =>
      return .none


@[inline]
partial def delabSample_Rewrite_topForw (appH : Expr) (appA : Array Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (Option (OptionProd Name Expr)) := do
  mtracing
  match appH with
  | .const h _ =>
      match delabRW_core h appA with
      | .none =>
          return .none
      | .some main ini =>
          mtrace on .zero with s!" main {← ppExpr main}"
          mtrace on .one with s!" ini {← ppExpr ini}"
          match ← main.pseudoConstSpe l1 l2 with
          | .some n => -- case of standard rw
            return .some <| .some n ini
          | _ => -- funky stuff like rw[(show _ from by _)] , .. or hyp fvar !
            return .some <| .none
  | _ =>
      return .none

@[inline]
partial def delabSample_Rewrite_topForw_withHyps (appH : Expr) (appA : Array Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (Option (OptionProd Name (List Expr))) := do
  mtracing
  match appH with
  | .const h _ =>
      match delabRW_core h appA with
      | .none =>
          return .none
      | .some main ini =>
          mtrace on .zero with s!" main {← ppExpr main}"
          mtrace on .one with s!" ini {← ppExpr ini}"
          match ← main.pseudoConstSpe l1 l2 with
          | .some n => -- case of standard rw
            let appH := main.getAppFn
            let args ← appH.withRelevantArgsBack l1 l2 appA [ini] (fun x y => return x :: y)
            return .some <| .some n args
          | _ => -- funky stuff like rw[(show _ from by _)] , .. or hyp fvar !
            return .some <| .none
  | _ =>
      return .none
