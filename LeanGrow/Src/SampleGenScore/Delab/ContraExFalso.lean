/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.SampleGenScore.Delab.InjNoConfAcyclic

open Lean Meta

/--
Also handles by_contra
todo (long term):  handle by_contra like by_cases for sampling
-/
@[inline]
partial def delabSample_ExFalso_core (appH : Expr) (appA : Array Expr)
  : MetaM (Option Expr) := do
  match appH with
  | .const k _ =>
    match k with
    | ``False.elim => return appA[1]!
    | ``Decidable.byContradiction => return appA[2]!
    | ``Classical.byContradiction => return appA[1]!
    | _ =>  return .none
  | _ => return .none




@[inline]
partial def delabSample_Contradiction_core (appH : Expr) (appA : Array Expr)
  (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (Option (List Expr)) := do
  match appH with
  | .const k _ =>
    if k == ``False.elim
    then
      match appA[1]! with
      | .app x y =>
          match x.getAppFn' with
          | .const h _ =>
            if h == ``noConfusion_of_Nat
            then return .some []
            else return .some [x,y]
          | _ => return .some [x,y] -- expected as fvars, my be inlined haves
      | _ => return .none
    else
      if k == ``absurd
      then
        match appA[2]!.getAppFn with
        | .const k _ =>
          if k == ``Eq.refl
          then return [appA[3]!]
          else
            match appA[3]!.getAppFn with
            | .const k _ =>
              if k == ``of_decide_eq_false
              then return [appA[2]!]
              else return .none
            | _ => return .none
        | _ =>
          match appA[3]!.getAppFn with
          | .const k _ =>
            if k == ``of_decide_eq_false
            then return [appA[2]!]
            else return .none
          | _ => return .none
      else
        delabSample_noConfusion_core appH appA l1 l2
  | _ => delabSample_noConfusion_core appH appA l1 l2
