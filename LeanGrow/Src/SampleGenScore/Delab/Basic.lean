

/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.SampleGenScore.Utils
import LeanGrow.Src.Utils.Lean.Blacklisting
import LeanGrow.Src.Utils.Lean.Expr.Basic

open Lean Meta


-- have let revert assert specialize define apply decide

@[inline]
def Lean.Name.shouldBeDelabedAsSpecialTerm (n : Name) : Bool :=
  n == ``Eq.ndrec || n == ``Eq.mp || n == ``Eq.mpr || n == ``congrArg || n == ``congrFun
  -- todo add more



@[inline]
partial def delabSample_Apply_core (appH : Expr) (appA : Array Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM ((Option Expr) × (List Expr)) := do
  let core := do
    let rarg ← appH.withRelevantArgsBack l1 l2 appA [] (fun x xs => return x :: xs)
    let ra ← (appH :: rarg).filterM (fun -- appH could be inlined have
      | .fvar fvid => do
        match ← fvid.GetDecl l1 l2 with
        | .ldecl .. => return true
        | _ => return false
      | x => return !x.isAtomic)
    if ← appH.isPseudoAtomic l1 l2
    then return .mk (.some (mkAppN appH appA)) ra
    else return .mk .none ra
  let .const h _ := appH | core
  if h == ``of_decide_eq_true
  then return .mk .none []
  else
    if h.shouldBeDelabedAsSpecialTerm
    then return .mk .none []
      -- **IMPORTANT** term delab should be here
    else core

@[inline]
partial def delabDig_Apply_core (appH : Expr) (appA : Array Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (List Expr) := do
  let core := do
    let rarg ← appH.withRelevantArgsBack l1 l2 appA [] (fun x xs => return x :: xs)
    return (appH :: rarg).filter (fun x => !x.isAtomic) -- appH could be inlined have
  let .const h _ := appH | core
  if h == ``of_decide_eq_true
  then return []
  else
    if h.shouldBeDelabedAsSpecialTerm
    then return []
      -- **IMPORTANT** term delab should be here
    else core

@[inline]
partial def delabSample_Apply_top
  (conjable : CTrie (List Nat))
  (appH : Expr) (appA : Array Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM SampleData := do
  match ← appH.pseudoConst l1 l2 with
  | .some n =>
    if n.blackListSampleDelta || n == ``of_decide_eq_true
    then return .none
    else
      match conjable.find? n.toString.toUTF8 with
      | .none =>
        return .thm n
      | .some poses =>
        let cjs := poses.foldl (fun A p => A.push appA[p]!) #[]
        return .thmC n cjs
  | _ => return .none


@[inline]
partial def delabSample_Apply_top_withHyps
  (appH : Expr) (appA : Array Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (SampleData × List Expr) := do
  match ← appH.pseudoConst l1 l2 with
  | .some n =>
    if n.blackListSampleDelta || n == ``of_decide_eq_true || n.shouldBeDelabedAsSpecialTerm
    then return (.none, [])
    else
      let rarg ← appH.withRelevantArgsBack l1 l2 appA [] (fun x xs => return x :: xs)
      let arg := rarg.filter (fun x => !x.isAtomic)
      return (.thm n, arg)
  | _ => return (.none, [])



@[inline]
def Lean.Expr.hasBvarZeroTwice (e : Expr) : Bool :=
  let rec go (d : Nat) (st : LBool) : Expr → LBool
    | .bvar i =>
        if i == d
        then
          match st with
          | .false => .undef
          | .undef => .true
          | t => t
        else
          st
    | .app l r =>
        let R := (go d st l)
        match R with
        | .false | .undef => go d R r
        | t => t
    | .lam _ l r _ | .forallE _ l r _ =>
        let R := (go d st l)
        match R with
        | .false | .undef => go (d+1) R r
        | t => t
    | .letE _ l r z _ =>
        let R := (go d st l)
        match R with
        | .false | .undef =>
            let M := (go d R r)
            match M with
            | .false | .undef => go (d+1) M z
            | t => t
        | t => t
    | .proj _ _ e | .mdata _ e => go d st e
    | _ => st
  match go 0 .false e with
  | .true => true
  | _ => false


@[inline]
def delabSample_HaveLet_core (binName : Name) (letT letV letB : Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (Prod4 (Option FVarId) Expr LocalContext LocalInstances) := do
  if (← IsProp letT l1 l2)
  then
    if letB.hasBvarZeroTwice
    then
      let desambig ← mkFreshId
      let .mk nfv l1 l2 ← WithLetDecl (binName ++ desambig) letT letV l1 l2
      let letB := Expr.instantiateBetaRevRange letB 0 1 #[(.fvar nfv)]
      return .mk nfv letB l1 l2
    else
      return .mk .none (letB.instantiateBetaRevRange 0 1 #[letV]) l1 l2
  else
    match ← IsClass? letT l1 l2 with
    | .some .. =>
      let desambig ← mkFreshId
      let .mk nfv l1 l2 ← WithLetDecl (binName ++ desambig) letT letV l1 l2
      let letB := Expr.instantiateBetaRevRange letB 0 1 #[(.fvar nfv)]
      return .mk nfv letB l1 l2
    | _ =>
      return .mk .none (letB.instantiateBetaRevRange 0 1 #[letV]) l1 l2

@[inline]
def delabDig_HaveLet_core (binName : Name) (letT letV letB : Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (Prod5 (Option FVarId) Expr (Option Expr) LocalContext LocalInstances) := do
  if (← IsProp letT l1 l2)
  then
    if letB.hasBvarZeroTwice
    then
      let desambig ← mkFreshId
      let .mk nfv l1 l2 ← WithLetDecl (binName ++ desambig) letT letV l1 l2
      let letB := Expr.instantiateBetaRevRange letB 0 1 #[(.fvar nfv)]
      return .mk nfv letB letV l1 l2
    else
      return .mk .none (letB.instantiateBetaRevRange 0 1 #[letV]) .none l1 l2
  else
    match ← IsClass? letT l1 l2 with
    | .some .. =>
      let desambig ← mkFreshId
      let .mk nfv l1 l2 ← WithLetDecl (binName ++ desambig) letT letV l1 l2
      let letB := Expr.instantiateBetaRevRange letB 0 1 #[(.fvar nfv)]
      return .mk nfv letB .none l1 l2
    | _ =>
      return .mk .none (letB.instantiateBetaRevRange 0 1 #[letV]) .none l1 l2



/-- assumes appA nonempty-/
@[inline]
partial def delabSample_AssertDefineRevert_core (appH : Expr) (appA : Array Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (Prod5 (List FVarId) (List Expr) (Option Expr) LocalContext LocalInstances) := do
  mtracing
  mtrace on .zero with s!" cal on appH : {← ppExpr appH}\nappA : {← appA.mapM ppExpr}"
  let rec reduceLetLike (h : Expr) (aIdx : Nat)
    (lifted : List FVarId) (l1 : LocalContext) (l2 : LocalInstances)
    : MetaM (Prod5 (List FVarId) Expr Nat LocalContext LocalInstances) := do
    match h with
    | .letE _ _ V B _ => reduceLetLike (B.instantiate1 V) aIdx lifted l1 l2
    | .lam _ letT letB _ =>
        if aIdx ≥ appA.size
        then return .mk lifted h aIdx l1 l2
        else
          let letV := appA[aIdx]!
          if (← IsProp letT l1 l2)
          then
            if letB.hasBvarZeroTwice
            then
              let desambig ← mkFreshId
              let .mk nfv l1 l2 ← WithLetDecl (`lamLetLike ++ desambig) letT letV l1 l2
              let letB := Expr.instantiateBetaRevRange letB 0 1 #[(.fvar nfv)]
              reduceLetLike letB (aIdx+1) (nfv :: lifted) l1 l2
            else
              reduceLetLike (letB.instantiateBetaRevRange 0 1 #[letV]) (aIdx+1) lifted l1 l2
          else
            match ← IsClass? letT l1 l2 with
            | .some .. =>
              let desambig ← mkFreshId
              let .mk nfv l1 l2 ← WithLetDecl (`lamLetLike ++ desambig) letT letV l1 l2
              let letB := Expr.instantiateBetaRevRange letB 0 1 #[(.fvar nfv)]
              reduceLetLike letB (aIdx+1) (nfv :: lifted) l1 l2
            | _ =>
              reduceLetLike (letB.instantiateBetaRevRange 0 1 #[letV]) (aIdx+1) lifted l1 l2
    | _ => return .mk lifted h aIdx l1 l2
  let .mk lifted h aIdx l1 l2 ← reduceLetLike appH 0 [] l1 l2
  if aIdx == appA.size
  then return .mk lifted [h] .none l1 l2
  else
    let appA := appA.drop aIdx
    let (delZet, rargs) ← delabSample_Apply_core h appA l1 l2
    return .mk lifted (if h.isAtomic then rargs else h :: rargs) delZet l1 l2


/-- assumes appA nonempty-/
@[inline]
partial def delabDig_AssertDefineRevert_core (appH : Expr) (appA : Array Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (Prod5 (List FVarId) (List Expr) (List Expr) LocalContext LocalInstances) := do
  mtracing
  mtrace on .zero with s!" cal on appH : {← ppExpr appH}\nappA : {← appA.mapM ppExpr}"
  let rec reduceLetLike (h : Expr) (aIdx : Nat)
    (lifted : List FVarId) (haveLikeProofs : List Expr) (l1 : LocalContext) (l2 : LocalInstances)
    : MetaM (Prod6 (List FVarId) Expr Nat (List Expr) LocalContext LocalInstances) := do
    match h with
    | .letE _ _ V B _ => reduceLetLike (B.instantiate1 V) aIdx lifted haveLikeProofs l1 l2
    | .lam _ letT letB _ =>
        if aIdx ≥ appA.size
        then return .mk lifted h aIdx haveLikeProofs l1 l2
        else
          let letV := appA[aIdx]!
          if (← IsProp letT l1 l2)
          then
            if letB.hasBvarZeroTwice
            then
              let desambig ← mkFreshId
              let .mk nfv l1 l2 ← WithLetDecl (`lamLetLike ++ desambig) letT letV l1 l2
              let letB := Expr.instantiateBetaRevRange letB 0 1 #[(.fvar nfv)]
              reduceLetLike letB (aIdx+1) (nfv :: lifted) (letV :: haveLikeProofs) l1 l2
            else
              reduceLetLike (letB.instantiateBetaRevRange 0 1 #[letV]) (aIdx+1) lifted haveLikeProofs l1 l2
          else
            match ← IsClass? letT l1 l2 with
            | .some .. =>
              let desambig ← mkFreshId
              let .mk nfv l1 l2 ← WithLetDecl (`lamLetLike ++ desambig) letT letV l1 l2
              let letB := Expr.instantiateBetaRevRange letB 0 1 #[(.fvar nfv)]
              reduceLetLike letB (aIdx+1) (nfv :: lifted) haveLikeProofs l1 l2
            | _ =>
              reduceLetLike (letB.instantiateBetaRevRange 0 1 #[letV]) (aIdx+1) lifted haveLikeProofs l1 l2
    | _ => return .mk lifted h aIdx haveLikeProofs l1 l2
  let .mk lifted h aIdx haveLikeProofs l1 l2 ← reduceLetLike appH 0 [] [] l1 l2
  if aIdx == appA.size
  then return .mk lifted [h] haveLikeProofs l1 l2
  else
    let appA := appA.drop aIdx
    let rargs ← delabDig_Apply_core h appA l1 l2
    return .mk lifted (if h.isAtomic then rargs else h :: rargs) haveLikeProofs l1 l2



/-- assumes appA nonempty-/
@[inline]
partial def delabSample_AssertDefineRevert_top
  (conjable : CTrie (List Nat))
  (appH : Expr) (appA : Array Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM SampleData := do
  mtracing
  mtrace on .zero with s!" cal on appH : {← ppExpr appH}\nappA : {← appA.mapM ppExpr}"
  let rec reduceLetLike (h : Expr) (aIdx : Nat)
    (l1 : LocalContext) (l2 : LocalInstances)
    : MetaM (Prod4 Expr Nat LocalContext LocalInstances) := do
    match h with
    | .letE _ _ V B _ => reduceLetLike (B.instantiate1 V) aIdx l1 l2
    | .lam _ letT letB _ =>
        if aIdx ≥ appA.size
        then return .mk h aIdx l1 l2
        else
          let letV := appA[aIdx]!
          if (← IsProp letT l1 l2)
          then
            if letB.hasBvarZeroTwice
            then
              let desambig ← mkFreshId
              let .mk nfv l1 l2 ← WithLetDecl (`lamLetLike ++ desambig) letT letV l1 l2
              let letB := Expr.instantiateBetaRevRange letB 0 1 #[(.fvar nfv)]
              reduceLetLike letB (aIdx+1) l1 l2
            else
              reduceLetLike (letB.instantiateBetaRevRange 0 1 #[letV]) (aIdx+1) l1 l2
          else
            match ← IsClass? letT l1 l2 with
            | .some .. =>
              let desambig ← mkFreshId
              let .mk nfv l1 l2 ← WithLetDecl (`lamLetLike ++ desambig) letT letV l1 l2
              let letB := Expr.instantiateBetaRevRange letB 0 1 #[(.fvar nfv)]
              reduceLetLike letB (aIdx+1) l1 l2
            | _ =>
              reduceLetLike (letB.instantiateBetaRevRange 0 1 #[letV]) (aIdx+1) l1 l2
    | _ => return .mk h aIdx l1 l2
  let .mk h skip l1 l2 ← reduceLetLike appH 0 l1 l2
  delabSample_Apply_top conjable h (appA.drop skip) l1 l2


@[inline]
partial def delabSample_AssertDefineRevert_top_withHyps
  (appH : Expr) (appA : Array Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (SampleData × List Expr) := do
  mtracing
  mtrace on .zero with s!" cal on appH : {← ppExpr appH}\nappA : {← appA.mapM ppExpr}"
  let rec reduceLetLike (h : Expr) (aIdx : Nat)
    (l1 : LocalContext) (l2 : LocalInstances)
    : MetaM (Prod4 Expr Nat LocalContext LocalInstances) := do
    match h with
    | .letE _ _ V B _ => reduceLetLike (B.instantiate1 V) aIdx l1 l2
    | .lam _ letT letB _ =>
        if aIdx ≥ appA.size
        then return .mk h aIdx l1 l2
        else
          let letV := appA[aIdx]!
          if (← IsProp letT l1 l2)
          then
            if letB.hasBvarZeroTwice
            then
              let desambig ← mkFreshId
              let .mk nfv l1 l2 ← WithLetDecl (`lamLetLike ++ desambig) letT letV l1 l2
              let letB := Expr.instantiateBetaRevRange letB 0 1 #[(.fvar nfv)]
              reduceLetLike letB (aIdx+1) l1 l2
            else
              reduceLetLike (letB.instantiateBetaRevRange 0 1 #[letV]) (aIdx+1) l1 l2
          else
            match ← IsClass? letT l1 l2 with
            | .some .. =>
              let desambig ← mkFreshId
              let .mk nfv l1 l2 ← WithLetDecl (`lamLetLike ++ desambig) letT letV l1 l2
              let letB := Expr.instantiateBetaRevRange letB 0 1 #[(.fvar nfv)]
              reduceLetLike letB (aIdx+1) l1 l2
            | _ =>
              reduceLetLike (letB.instantiateBetaRevRange 0 1 #[letV]) (aIdx+1) l1 l2
    | _ => return .mk h aIdx l1 l2
  let .mk h skip l1 l2 ← reduceLetLike appH 0 l1 l2
  delabSample_Apply_top_withHyps h (appA.drop skip) l1 l2
