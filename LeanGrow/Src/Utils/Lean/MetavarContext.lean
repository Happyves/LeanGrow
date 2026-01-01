
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Lean.Meta.Basic
import Batteries.Tactic.OpenPrivate
import LeanGrow.Src.Data.Amalgames


open Lean Meta

open private Lean.Meta.mkFreshExprMVarAtCore from Lean.Meta.Basic

@[inline]
def Lean.MetavarContext.addExprMVarDeclI (mctx : MetavarContext)
    (mvarId : MVarId)
    (userName : Name)
    (lctx : LocalContext)
    (localInstances : LocalInstances)
    (type : Expr)
    (kind : MetavarKind := MetavarKind.natural)
    (numScopeArgs : Nat := 0)
    (index : Nat) : MetavarContext :=
  { mctx with
    mvarCounter := mctx.mvarCounter + 1
    decls       := mctx.decls.insert mvarId {
      depth := mctx.depth
      index := index
      userName
      lctx
      localInstances
      type
      kind
      numScopeArgs }
    userNames := if userName.isAnonymous then mctx.userNames else mctx.userNames.insert userName mvarId }

@[inline]
def Lean.Meta.mkFreshExprMVarAtCoreI
    (mvarId : MVarId) (lctx : LocalContext) (localInsts : LocalInstances) (type : Expr) (kind : MetavarKind) (userName : Name) (numScopeArgs : Nat) (index : Nat) : MetaM Expr := do
  modifyMCtx fun mctx => mctx.addExprMVarDeclI mvarId userName lctx localInsts type kind numScopeArgs index
  return mkMVar mvarId


@[inline]
def mkMvarStdNoCoE (n : Name) (type : Expr) : MetaM Expr :=
  Lean.Meta.mkFreshExprMVarAtCore ⟨n⟩ {} {} type .natural n 0

@[inline]
def mkMvarStdNoCoI (n : Name) (type : Expr) : MetaM MVarId := do
  let mv : MVarId := ⟨n⟩
  let _ ← Lean.Meta.mkFreshExprMVarAtCore mv {} {} type .natural n 0
  return mv

@[inline]
def mkMvarStdIndexNoCoE (n : Name) (type : Expr) (index : Nat) : MetaM Expr :=
  Lean.Meta.mkFreshExprMVarAtCoreI ⟨n⟩ {} {} type .natural n 0 index

@[inline]
def mkMvarStdIndexNoCoI (n : Name) (type : Expr) (index : Nat) : MetaM MVarId := do
  let mv : MVarId := ⟨n⟩
  let _ ← Lean.Meta.mkFreshExprMVarAtCoreI mv {} {} type .natural n 0 index
  return mv


@[inline]
def loadMVarsNoCoA (data : Array (Name × Expr)) : MetaM Unit := do
  for (n,t) in data do
    let _ ← Lean.Meta.mkFreshExprMVarAtCore ⟨n⟩ {} {} t .natural n 0
  pure ()

@[inline]
def loadMVarsWiCoA (data : Array (Name × Expr)) (lctx : LocalContext) (lins : LocalInstances) : MetaM Unit := do
  for (n,t) in data do
    let _ ← Lean.Meta.mkFreshExprMVarAtCore ⟨n⟩ lctx lins t .natural n 0
  pure ()

@[inline]
def loadMVarsNoCoL (data : List (Name × Expr)) : MetaM Unit := do
  for (n,t) in data do
    let _ ← Lean.Meta.mkFreshExprMVarAtCore ⟨n⟩ {} {} t .natural n 0
  pure ()

@[inline]
def loadMVarsWiCoL (data : List (Name × Expr)) (lctx : LocalContext) (lins : LocalInstances) : MetaM Unit := do
  for (n,t) in data do
    let _ ← Lean.Meta.mkFreshExprMVarAtCore ⟨n⟩ lctx lins t .natural n 0
  pure ()


@[inline]
def loadMVarsIndexedNoCoA (data : Array (Prod3 Name Expr Nat)) : MetaM Unit := do
  for ⟨n,t,i⟩ in data do
    let _ ← Lean.Meta.mkFreshExprMVarAtCoreI ⟨n⟩ {} {} t .natural n 0 i
  pure ()

@[inline]
def loadMVarsWiIndexNoCoA (data : Array (Name × Expr)) (start : Nat) : MetaM Unit := do
  let mut i := start
  for (n,t) in data do
    let _ ← Lean.Meta.mkFreshExprMVarAtCoreI ⟨n⟩ {} {} t .natural n 0 i
    i := i + 1
  pure ()


@[inline]
def mkLevelMVarOfName (n : Name) : MetaM Level := do
  modifyMCtx fun mctx => mctx.addLevelMVarDecl ⟨n⟩
  return .mvar ⟨n⟩


@[inline]
def mkFreshLevelMVarId : MetaM LMVarId := do
  let mvarId ← mkFreshLMVarId
  modifyMCtx fun mctx => mctx.addLevelMVarDecl mvarId;
  return mvarId

@[inline]
def mkFreshLevelMVarsWN (num : Nat) : MetaM (List Level × Array LMVarId) :=
  num.foldM (init := ([],#[])) fun _ _ (us,ns) => do
    let lid ← mkFreshLevelMVarId
    return ((.mvar lid) :: us, ns.push lid)

@[inline]
def mkFreshLevelMVarsForWN (info : ConstantInfo) : MetaM (List Level × Array LMVarId) :=
  mkFreshLevelMVarsWN info.numLevelParams

@[inline]
def mkFreshTaggedLevelMVarId (tag : String) : MetaM LMVarId := do
  let mvarId := ⟨.str (← mkFreshId) tag⟩
  modifyMCtx fun mctx => mctx.addLevelMVarDecl mvarId;
  return mvarId

@[inline]
def mkFreshTaggedLevelMVarsWN (tag : String) (num : Nat) : MetaM (List Level × Array LMVarId) :=
  num.foldM (init := ([],#[])) fun _ _ (us,ns) => do
    let lid ← mkFreshTaggedLevelMVarId tag
    return ((.mvar lid) :: us, ns.push lid)

@[inline]
def mkFreshTaggedLevelMVarsForWN (tag : String) (info : ConstantInfo) : MetaM (List Level × Array LMVarId) :=
  mkFreshTaggedLevelMVarsWN tag info.numLevelParams

@[inline]
def mkFreshExprMVarTagAt (tag : String)
    (lctx : LocalContext) (localInsts : LocalInstances) (type : Expr)
    (kind : MetavarKind := MetavarKind.natural) (userName : Name := Name.anonymous) (numScopeArgs : Nat := 0)
    : MetaM Expr := do
  mkFreshExprMVarAtCoreI ⟨.str (← mkFreshId) tag⟩ lctx localInsts type kind userName numScopeArgs (← getMCtx).depth

@[inline]
private def mkFreshExprMVarTagCore (tag : String)  (type : Expr) (kind : MetavarKind)
  (userName : Name) (lctx : LocalContext) (lins : LocalInstances) : MetaM Expr := do
  mkFreshExprMVarTagAt tag lctx lins type kind userName

@[inline]
private def mkFreshExprMVarTagImpl (tag : String)  (type? : Option Expr) (kind : MetavarKind) (userName : Name)
  (lctx : LocalContext) (lins : LocalInstances) : MetaM Expr :=
  match type? with
  | some type => mkFreshExprMVarTagCore tag type kind userName lctx lins
  | none      => do
    let u := .mvar <| ← mkFreshTaggedLevelMVarId tag
    let type ← mkFreshExprMVarTagCore tag (mkSort u) MetavarKind.natural Name.anonymous lctx lins
    mkFreshExprMVarTagCore tag type kind userName lctx lins

@[inline]
def mkFreshExprMVarTag (tag : String)  (type? : Option Expr) (lctx : LocalContext) (lins : LocalInstances)
  (kind := MetavarKind.natural) (userName := Name.anonymous) : MetaM Expr :=
  mkFreshExprMVarTagImpl tag type? kind userName lctx lins


@[inline]
def loadLMVarsNoCoA (data : Array (LMVarId)) : MetaM Unit := do
  for n in data do
    modifyMCtx fun mctx => mctx.addLevelMVarDecl n
  pure ()


#check MVarId.modifyLCtx


-- # Printing


def printMetaDecls : MetaM String := do
  let mctx ← getMCtx
  let lvls := mctx.lDepth.toList
  let pl := String.intercalate "\n" (lvls.map (fun x => s!"{repr x}"))
  let mvs := mctx.decls.toList.map (fun (x,y) => (x,y.type))
  let inter ← mvs.mapM (fun (x,y) => return s!"{repr x} : {← ppExpr y}")
  let pmv := String.intercalate "\n" ( pl :: inter)
  return pmv
