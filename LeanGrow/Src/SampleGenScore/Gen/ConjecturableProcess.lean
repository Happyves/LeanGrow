
/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Lean.Meta.Basic
import LeanGrow.Src.Utils.Lean.Expr.Basic


-- **Duplication from Caching.Format.Types**

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


def MCtxData.loadNoCo (data : MCtxData) : MetaM Unit := do
  modifyMCtx (fun mc =>
    let mc := {mc with lDepth := data.lDepth.foldl (fun R (i, j) => R.insert i j) mc.lDepth}
    let mc := {mc with userNames := data.userNames.foldl (fun R (i, j) => R.insert i j) mc.userNames}
    let mc :=  data.decls.foldl (fun R (i, j) =>
      {R with decls := R.decls.insert i ({j with index := R.mvarCounter}), mvarCounter := R.mvarCounter + 1 }
      ) mc
    mc)


inductive ThmFormat where
| std (name : Name ⊕ FVarId)
      (lvlParamsNum : Nat)
      (predicate? : Bool)
      (hyps : Array HypType)
      (mctx : MCtxData)
      (hypsNum : Nat)
      (goal : Expr)
      (sinks : List Nat)
      (badFo badBa : Bool)
| rw  (name : Name ⊕ FVarId)
      (lvlParamsNum : Nat)
      (kind : RWkind)
      (goal : Expr)
      (replacement : Expr)
      (hyps : Array HypType)
      (mctx : MCtxData)
      (hypsNum : Nat)
      (sinks : List Nat)
      (badFo badBa : Bool)
      (simpliFactor : Float)


@[inline]
def ThmFormat.sinks : ThmFormat → List Nat
  | .std _ _ _ _ _ _ _  hyps .. => hyps
  | .rw _ _  _  _ _  _ _ _ hyps .. => hyps



-- **end of duplication from Caching.Format.Types**

-- Wait til fix of ctries and all before bringing this over
-- Also, test ↓, since we haven't et, as were missing the process infrastructure

#check Or.rec
#check Eq.trans
#check Int.le_trans

#check Classical.byCases
#check Classical.byContradiction

/-- An argument is conjecturable for a back-step if it isn't a proof (its type is a prop),
it isn't in the goal, and it has no other non-proof-argument dependning on it.
-/
def getConjecturablePos_ofProcessed (hyps : Array HypType) (goal : Expr) : MetaM (List Nat) := do
  let gdeps := goal.onAllSubtermsFold [] (fun e l =>
    match e with
    | .mvar (.mk (.num _ pos)) => l.insert pos
    | _ => l
    )
  let mut res := []
  let mut i := 0
  for h in hyps do
    if gdeps.contains i
    then
      i := i+1
    else
      match h with
      | .inst .. => i := i+1
      | .reg T =>
        if !(← IsProp T (← getLCtx) (← getLocalInstances))
        then
          let tdeps := T.onAllSubtermsFold [] (fun e l =>
            match e with
            | .mvar (.mk (.num _ pos)) => l.insert pos
            | _ => l
            )
          res := i :: (res.filter (fun x => !(tdeps.contains x)))
        i := i+1
  return res.mergeSort (· ≤ ·) -- important that sorted !

#check 1


partial def getConjecturablePos (type : Expr) : MetaM (List Nat) := do
  let rec process (i : Nat) (hyps : Array Expr) (T : Expr) : MetaM (Expr × Array Expr) := do
    -- **To check** : matches process (wrt let and whnf, among others)
    match T with
    | .forallE _ t b bi =>
      let mv ← mkMvarStdNoCoE (.num `dummy i) t
      let b := Expr.instantiate1 b mv
      match bi with
      | .instImplicit =>
        process (i+1) hyps b
      | _ =>
        process (i+1) (hyps.push t) b
    | .letE _ _ v b _ =>
      process i hyps (Expr.instantiate1 b v)
    | _ => return (T,hyps)
  let .mk goal hyps ← process 0 #[] type
  let gdeps := goal.onAllSubtermsFold [] (fun e l =>
    match e with
    | .mvar (.mk (.num _ pos)) => l.insert pos
    | _ => l
    )
  let mut res := []
  let mut i := 0
  for T in hyps do
    if gdeps.contains i
    then
      i := i+1
    else
      if !(← IsProp T (← getLCtx) (← getLocalInstances))
      then
        let tdeps := T.onAllSubtermsFold [] (fun e l =>
          match e with
          | .mvar (.mk (.num _ pos)) => l.insert pos
          | _ => l
          )
        res := i :: (res.filter (fun x => !(tdeps.contains x)))
      i := i+1
  return res.mergeSort (· ≤ ·) -- important that sorted !
