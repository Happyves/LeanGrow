/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.SampleGenScore.Utils

open Lean Meta




@[inline]
partial def delabSample_noConfusion_core (appH : Expr) (appA : Array Expr)
  (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (Option (List Expr)) := do
  match appH with
  | .const n _ =>
    if n == ``False.elim
    then
      let f := appA[1]!
      let h := f.getAppFn'
      match h with
      | .const n _ =>
        if n == ``noConfusion_of_Nat then return .some [] else return .none
      | _ => return .none
    else
      match n with
      | .str _ k =>
        if k == "noConfusion"
        then
          let res ← (mkAppN appH appA).getRelevantArgsBack l1 l2
          return .some res.toList
        else
          return .none
      | _ => return .none
  | _ => return .none


#check False.elim
#check noConfusion_of_Nat
#check List.noConfusion

/-- can occur as app or lam-/
@[inline]
partial def delabSample_Injection_core (e : Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (Prod3 (Option (List Expr)) LocalContext LocalInstances) := do
  let e := e.headBeta
  let .mk b _ l1 l2 ← LambdaLetTelescope e 0 l1 l2
  let h := b.getAppFn'
  let as := b.getAppArgs
  let res ← delabSample_noConfusion_core h as l1 l2
  return .mk res l1 l2

/-- May return a have-bound-fvar or an inlined one-/
@[inline]
partial def delabSample_Acyclic_core (appH : Expr) (appA : Array Expr)
  : MetaM (Option Expr) := do
  match appH with
  | .const n _ =>
    if n == ``False.elim
    then
      let nx := appA[1]!
      match nx with
      | .app _ nx =>
          match nx.getAppFn' with
          | .const k _ =>
            if k == ``Nat.lt_of_lt_of_eq
            then
              let nx := nx.getArg! 4
              match nx.getAppFn' with
              | .const k _ =>
                if k == ``congrArg
                then
                  let fas := nx.getAppArgs
                  match fas[4]!.getAppFn' with
                  | .const k _ =>
                    if k == ``sizeOf
                    then
                      let fin := fas[5]!
                      match fin.getAppFn' with
                      | .const k _ =>
                        if k == ``Eq.symm
                        then
                          return .some <| fin.getArg! 3
                        else
                          return .none
                      | _ => return .none
                    else
                      return .none
                  | _ => return .none
                else
                  return .none
              | _ => return .none
            else
              return .none
          | _ => return .none
      | _ => return .none
    else
      return .none
  | _ => return .none

#check Eq.symm
