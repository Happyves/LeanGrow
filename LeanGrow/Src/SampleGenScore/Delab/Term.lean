

/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.SampleGenScore.Delab.Rewrite
import LeanGrow.Src.Utils.Lean.Blacklisting
import LeanGrow.Src.Utils.Lean.Expr.Basic

open Lean Meta


def mathlibTactic? : Name → Bool
  | .str .anonymous s1 =>
    s1 == "Lean" -- Lean.Omega for example
  | .str (.str .anonymous s1) s2 =>
    s1 == "Mathlib" && s2 == "Tactic"
  -- todo : Batteries ?
  | .str p _ => mathlibTactic? p
  | .num p _ => mathlibTactic? p
  | .anonymous => false


@[inline]
partial def delabSample_Term_core (head : Name) (appH : Expr) (appA : Array Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (Prod5 (List FVarId) (Option (List Expr)) (Option Expr) LocalContext LocalInstances) := do
  let rw? : OptionProd Expr Expr :=
    match head with
    | ``Eq.ndrec | ``Eq.rec =>
      .some (consumeSymmPropext appA[5]!) appA[3]!
    | ``Eq.mpr | ``Eq.mp =>
      .some (consumeSymmPropext appA[2]!) appA[3]!
    | _ => .none
  match rw? with
  | .some main ini => -- same as rw
    let appH := main.getAppFn
    let appA := main.getAppArgs
    if ← appH.isPseudoAtomic l1 l2
    then -- case of standard rw
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
  | .none =>
      match head with
      | ``inferInstance =>
        return .mk [] (.some []) .none l1 l2
      | ``Function.comp =>
        let nh := Expr.app appA[3]! appA[4]!
        return .mk [] (.some [mkAppN nh (appA.drop 5)]) .none l1 l2
      | _ => -- same as apply core
        if head.blackListSampleDelta || head == ``of_decide_eq_true || mathlibTactic? head
        then
          return .mk [] (.some []) .none l1 l2
        else
          let rarg ← appH.withRelevantArgsBack l1 l2 appA [] (fun x xs => return x :: xs)
          let ra ← (appH :: rarg).filterM (fun -- appH could be inlined have
            | .fvar fvid => do
              match ← fvid.GetDecl l1 l2 with
              | .ldecl .. => return true
              | _ => return false
            | x => return !x.isAtomic)
          if ← appH.isPseudoAtomic l1 l2
          then return .mk [] (.some ra) (.some (mkAppN appH appA)) l1 l2
          else return .mk [] ra .none l1 l2


@[inline]
partial def delabDig_Term_core (head : Name) (appH : Expr) (appA : Array Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (Option (List Expr)) := do
  let rw? : OptionProd Expr Expr :=
    match head with
    | ``Eq.ndrec | ``Eq.rec =>
      .some (consumeSymmPropext appA[5]!) appA[3]!
    | ``Eq.mpr | ``Eq.mp =>
      .some (consumeSymmPropext appA[2]!) appA[3]!
    | _ => .none
  match rw? with
  | .some main ini => -- same as rw
    let appH := main.getAppFn
    let appA := main.getAppArgs
    if ← appH.isPseudoAtomic l1 l2
    then -- case of standard rw
      let rarg ← appH.withRelevantArgsBack l1 l2 appA [] (fun x xs => return x :: xs)
      return (ini :: rarg).filter (fun x => !x.isAtomic)
    else -- funky stuff like rw[(show _ from by _)]
      return (if ini.isAtomic then [main] else [main,ini])
  | .none =>
      match head with
      | ``inferInstance =>
        return (.some [])
      | ``Function.comp =>
        let nh := Expr.app appA[3]! appA[4]!
        return (.some [mkAppN nh (appA.drop 5)])
      | _ => --same as apply
        if head.blackListSampleDelta || head == ``of_decide_eq_true || mathlibTactic? head
        then
          return .some []
        else
          let rarg ← appH.withRelevantArgsBack l1 l2 appA [] (fun x xs => return x :: xs)
          return (appH :: rarg).filter (fun x => !x.isAtomic)



@[inline]
partial def delabSample_Term_topBack
  (conjable : CTrie (List Nat))
  (head : Name) (appH : Expr) (appA : Array Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (Option SampleData) := do
  let rw? : OptionProd Expr Expr :=
    match head with
    | ``Eq.ndrec | ``Eq.rec =>
      .some (consumeSymmPropext appA[5]!) appA[3]!
    | ``Eq.mpr | ``Eq.mp =>
      .some (consumeSymmPropext appA[2]!) appA[3]!
    | _ => .none
  match rw? with
  | .some main _ => -- same as rw
      let appH := main.getAppFn
      match ← appH.pseudoConst l1 l2 with
      | .some n => -- case of standard rw
          match conjable.find? n.toString.toUTF8 with
          | .none =>
            return .some <| .thm n
          | .some poses =>
            let cjs := poses.foldl (fun A p => A.push appA[p]!) #[]
            return .some <| .thmC n cjs
      | _ => -- funky stuff like rw[(show _ from by _)]
        return .some <| .none
  | .none =>
      match head with
      | ``inferInstance | ``Function.comp =>
        return (.some .none)
      | _ => --same as apply
        match ← appH.pseudoConst l1 l2 with
        | .some n =>
          if n.blackListSampleDelta || n == ``of_decide_eq_true || mathlibTactic? n
          then return .none
          else
            match conjable.find? n.toString.toUTF8 with
            | .none =>
              return .some <| .thm n
            | .some poses =>
              let cjs := poses.foldl (fun A p => A.push appA[p]!) #[]
              return .some <| .thmC n cjs
        | _ => return .none


@[inline]
partial def delabSample_Term_topForw
  (head : Name) (appH : Expr) (appA : Array Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (Option (Name ⊕ OptionProd Name Expr)) := do
  let rw? : OptionProd Expr Expr :=
    match head with
    | ``Eq.ndrec | ``Eq.rec =>
      .some (consumeSymmPropext appA[5]!) appA[3]!
    | ``Eq.mpr | ``Eq.mp =>
      .some (consumeSymmPropext appA[2]!) appA[3]!
    | _ => .none
  match rw? with
  | .some main ini => -- same as rw
      let appH := main.getAppFn
      match ← appH.pseudoConst l1 l2 with
      | .some n => -- case of standard rw
        return .some <| .inr <| .some n ini
      | _ => -- funky stuff like rw[(show _ from by _)] , .. or hyp fvar !
        return .some <| .inr <| .none
  | .none =>
      match head with
      | ``inferInstance | ``Function.comp =>
        return (.some <| .inr .none)
      | _ => --same as apply
        match ← appH.pseudoConst l1 l2 with
        | .some n =>
          if n.blackListSampleDelta || n == ``of_decide_eq_true || mathlibTactic? n
          then return .some <| .inr .none
          else
            return .some <| .inl n
        | _ => return .none


@[inline]
partial def delabSample_Term_topForw_withHyps
  (head : Name) (appH : Expr) (appA : Array Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (SampleData × (List Expr)) := do
  let rw? : OptionProd Expr Expr :=
    match head with
    | ``Eq.ndrec | ``Eq.rec =>
      .some (consumeSymmPropext appA[5]!) appA[3]!
    | ``Eq.mpr | ``Eq.mp =>
      .some (consumeSymmPropext appA[2]!) appA[3]!
    | _ => .none
  match rw? with
  | .some main ini => -- same as rw
      let appH := main.getAppFn
      match ← appH.pseudoConst l1 l2 with
      | .some n => -- case of standard rw
        let args ← appH.withRelevantArgsBack l1 l2 appA [ini] (fun x y => return x :: y)
        return (.thm n, args)
      | _ => -- funky stuff like rw[(show _ from by _)] , .. or hyp fvar !
        return (.none, [])
  | .none =>
      match head with
      | ``inferInstance | ``Function.comp =>
        return (.none, [])
      | _ => --same as apply
        match ← appH.pseudoConst l1 l2 with
        | .some n =>
          if n.blackListSampleDelta || n == ``of_decide_eq_true || mathlibTactic? n
          then return (.none, [])
          else
            let rarg ← appH.withRelevantArgsBack l1 l2 appA [] (fun x xs => return x :: xs)
            let arg := rarg.filter (fun x => !x.isAtomic)
            return (.thm n, arg)
        | _ => return (.none, [])
