


/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.SampleGenScore.Utils
import LeanGrow.Src.Utils.Lean.Expr.Basic

open Lean Meta



@[inline]
partial def delabSample_Matcher_core (appH : Expr) (appA : Array Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (Prod3 (Option (List Expr)) LocalContext LocalInstances) := do
  let .const h _ := appH | return .mk .none l1 l2
  if ← isMatcher h
  then
    withLCtx l1 l2 <| do
      let .some matin ← getMatcherInfo? h | return .mk .none l1 l2
      let mut haves? := []
      for i in matin.getDiscrRange do
        let H := appA[i]!
        if ← isProof H
        then haves? := H :: haves?
      return .mk (.some haves?) l1 l2
  else
    return .mk .none l1 l2


#check 1


@[inline]
partial def delabDig_Matcher_core (appH : Expr) (appA : Array Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (Prod3 (Option (List Expr)) LocalContext LocalInstances) := do
  let .const h _ := appH | return .mk .none l1 l2
  if ← isMatcher h
  then
    withLCtx l1 l2 <| do
      let .some matin ← getMatcherInfo? h | return .mk .none l1 l2
      let mut nex := []
      for i in matin.getDiscrRange do
        let H := appA[i]!
        if ← isProof H
        then nex := H :: nex
      for i in matin.getAltRange do
        let H := appA[i]!
        match H with
        | .lam _ (.const u? _) b _ =>
          if u? == ``Unit
          then nex := b :: nex
          else nex := H :: nex
        | _ =>
          nex := H :: nex
      return .mk (.some nex) l1 l2
  else
    return .mk .none l1 l2


@[inline]
partial def delabSample_Matcher_top (appH : Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (Prod3 Bool LocalContext LocalInstances) := do
  let .const h _ := appH | return .mk false l1 l2
  if ← isMatcher h
  then
    return .mk true l1 l2
  else
    return .mk false l1 l2
