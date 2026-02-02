
/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.SampleGenScore.Utils

open Lean Meta



@[inline]
partial def delabSample_Calc_top
  (l1 : LocalContext) (l2 : LocalInstances)
  (appH : Expr) (appA : Array Expr)
  : MetaM (Option SampleData) := do
  mtracing
  --: MetaM (Prod (Option (List Expr)) (Option Expr)) := do
  match appH with
  | .const h _ =>
    if h == ``Trans.trans
    then
      let rec getBody : Expr → Expr
        | .lam _ _ b _ => getBody b
        | x => x
      let core := do
        let toRed := (mkAppRange appH 0 7 appA)
        mtrace on .zero with s!" toRed {← ppExpr toRed}"
        let Real ← WhnfI toRed l1 l2
        mtrace on .zero with s!" Real {← ppExpr Real}"
        let .const real _ := (getBody Real).getAppFn' | return .some .none -- unexpected, but fail silently
        mtrace on .zero with s!" real {real}"
        return .some <| .thmC real #[appA[8]!]
      mtrace on .zero with s!" relations {← ppExpr appA[3]!} {← ppExpr appA[4]!}"
      match appA[3]!.getAppFn' with
      | .const h _ =>
        if h == `Eq
        then
          match appA[4]!.getAppFn' with
          | .const h _ =>
            if h == ``Eq
            then return .some <| .thmC ``Eq.trans #[appA[8]!]
            else return .some .none -- expect instTransEq
          | _ =>
            return .some .none -- expect instTransEq
        else
          match appA[4]!.getAppFn' with
          | .const h _ =>
            if h == `Eq
            then return .some .none -- expect instTransEq_1
            else core
          | _ =>
            core
      | _ =>
        match appA[4]!.getAppFn' with
        | .const h _ =>
          if h == `Eq
          then return .some .none -- expect instTransEq_1
          else core
        | _ =>
          core
    else
      return .none
  | _ =>
    return .none



@[inline]
partial def delabSample_Calc_core
  (appH : Expr) (appA : Array Expr)
  : MetaM (Option (List Expr)) := do
  match appH with
  | .const h _ =>
    if h == ``Trans.trans
    then
      return .some [appA[10]!, appA[11]!]
    else
      return .none
  | _ =>
    return .none
