
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Lean.Meta.Basic
import LeanGrow.Src.Utils.Lean.Expr.Basic


open Lean Meta

inductive HypType where
| reg (type : Expr)
| inst (type : Expr)
deriving Inhabited,Repr, BEq


inductive RWkind where
| eq_mp | eq_mpr | iff_mp | iff_mpr
deriving Inhabited,Repr, BEq


structure MCtxData where
  lDepth         : Array (LMVarId × Nat)
  decls          : Array (MVarId × MetavarDecl)
  userNames      : Array (Name × MVarId)
deriving Inhabited


def MCtxData.load (data : MCtxData) : MetaM Unit := do
  let ltx ← getLCtx
  let linst ← getLocalInstances
  modifyMCtx (fun mc =>
    let mc := {mc with lDepth := data.lDepth.foldl (fun R (i, j) => R.insert i j) mc.lDepth}
    let mc := {mc with userNames := data.userNames.foldl (fun R (i, j) => R.insert i j) mc.userNames}
    let mc :=  data.decls.foldl (fun R (i, j) =>
      {R with decls := R.decls.insert i ({j with lctx := ltx, localInstances := linst, index := R.mvarCounter}), mvarCounter := R.mvarCounter + 1 }
      ) mc
    mc) -- *Note* I'm guessing this makes linear use ?


def MCtxData.load' (data : MCtxData) : MetaM Unit := do
  let ltx ← getLCtx
  let linst ← getLocalInstances
  modifyMCtx (fun mc => {mc with lDepth := data.lDepth.foldl (fun R (i, j) => R.insert i j) mc.lDepth})
  modifyMCtx (fun mc =>  {mc with userNames := data.userNames.foldl (fun R (i, j) => R.insert i j) mc.userNames})
  data.decls.foldlM (fun _ (i, j) => do
      modifyMCtx (fun R =>  {R with decls := R.decls.insert i ({j with lctx := ltx, localInstances := linst, index := R.mvarCounter}), mvarCounter := R.mvarCounter + 1 })
      ) ()


inductive ThmFormat where
| std (name : Name ⊕ FVarId)
      (lvlParamsNum : Nat)
      (predicate? : Bool)
      (hyps : Array HypType)
      (mctx : MCtxData)
      (hypsNum : Nat)
      (goal : Expr)
      (sinks : List Nat)
| rw  (name : Name ⊕ FVarId)
      (lvlParamsNum : Nat)
      (kind : RWkind)
      (goal : Expr)
      (replacement : Expr)
      (hyps : Array HypType)
      (mctx : MCtxData)
      (hypsNum : Nat)
      (sinks : List Nat)

instance : Inhabited ThmFormat where
  default :=
    .std (.inl `defaultDummyThmFormat) 0 false #[] default 0 (failExpr "Inhabited ThmFormat") []



@[inline]
def ThmFormat.hypsTypes : ThmFormat → Array Expr
  | .std _ _ _  hyps .. => hyps.map (fun | .reg t | .inst t => t)
  | .rw _ _  _  _ _ hyps .. => hyps.map (fun | .reg t | .inst t => t)


@[inline]
def ThmFormat.sinks : ThmFormat → List Nat
  | .std _ _ _ _ _ _ _  hyps => hyps
  | .rw _ _  _  _ _  _ _ _ hyps => hyps



@[inline]
def ThmFormat.hyps : ThmFormat → Array HypType
  | .std _ _ _  hyps .. => hyps
  | .rw _ _  _  _ _ hyps .. => hyps


@[inline]
def ThmFormat.mctx : ThmFormat → MCtxData
  | .std _ _ _ _ mctx .. => mctx
  | .rw _ _ _  _ _ _ mctx .. => mctx


@[inline]
def ThmFormat.goal : ThmFormat → Expr
  | .std _ _ _ _ _ _ mctx .. => mctx
  | .rw _ _ _ mctx .. => mctx


@[inline]
def ThmFormat.hypsNum : ThmFormat → Nat
  | .std _ _ _ _ _ mctx .. => mctx
  | .rw _ _ _ _ _ _ _ mctx .. => mctx


@[inline]
def HypType.type : HypType → Expr
| .reg (type : Expr) | .inst (type : Expr) => type


@[inline]
def ThmFormat.lvlParamsNum : ThmFormat → Nat
  | .std _   hyps .. => hyps
  | .rw _ hyps .. => hyps


@[inline]
def ThmFormat.name : ThmFormat → Name ⊕ FVarId
  | .std   hyps .. => hyps
  | .rw hyps .. => hyps


instance : Repr ThmFormat where
  reprPrec := fun x y => instReprString.reprPrec s!"{repr x.name}" y
