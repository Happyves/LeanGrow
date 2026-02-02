
/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.SampleGenScore.Utils

open Lean Meta


def suspectedHCongrHead? (e : Expr) : Bool :=
  let rec getBody : Expr → Expr
    | .lam _ _ b _ => getBody b
    | x => x
  Id.run <| do
    let b := getBody e
    let .const h _ := b.getAppFn' | return false
    match h with
    | ``Eq.refl | ``HEq.refl | ``Eq.casesOn | ``HEq.casesOn | ``Eq.rec
    | ``Eq.ndrec | ``HEq.rec | ``HEq.ndrec => return true
    | _ => return false



def delabSample_CongrConvert_core
  (e : Expr) (l1 : LocalContext) (l2 : LocalInstances) :
  MetaM (Prod4 (List FVarId) (Option (List Expr)) LocalContext LocalInstances) := do
  let h := e.getAppFn'
  match h with
  | .lam .. =>
    if suspectedHCongrHead? h
    then
      let ras ← e.getRelevantArgsBack l1 l2
      return .mk [] (.some ras.toList) l1 l2
    else
      return .mk [] .none l1 l2
  | .const n _ =>
    match n with
    | ``Eq.mp | ``Eq.mpr => -- for convert ; should run after rw-delab
      let congr := e.getArg! 2
      let T ← InferType congr l1 l2
      let .mk fv l1 l2 ← WithLetDeclU `congrConv T congr l1 l2
      return .mk [fv] (.some []) l1 l2
    | _ => -- we want all other cases to be treated as apply-s
      return .mk [] .none l1 l2
  | _ =>
    return .mk [] .none l1 l2


def delabDig_CongrConvert_core
  (e : Expr) (l1 : LocalContext) (l2 : LocalInstances) :
  MetaM (Prod4 (List Expr) (Option (List Expr)) LocalContext LocalInstances) := do
  let h := e.getAppFn'
  match h with
  | .lam .. =>
    if suspectedHCongrHead? h
    then
      let ras ← e.getRelevantArgsBack l1 l2
      return .mk [] (.some ras.toList) l1 l2
    else
      return .mk [] .none l1 l2
  | .const n _ =>
    match n with
    | ``Eq.mp | ``Eq.mpr => -- for convert ; should run after rw-delab
      let congr := e.getArg! 2
      return .mk [congr] (.some []) l1 l2
    | _ => -- we want all other cases to be treated as apply-s
      return .mk [] .none l1 l2
  | _ =>
    return .mk [] .none l1 l2
