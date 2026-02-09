
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Utils.Lean.Expr.Basic
import LeanGrow.Src.Utils.LeanGrow.Expr


open Lean Meta



structure RecursorCache where
  name : Name
  term : Expr
  lvlLoad : Array LMVarId
  argLoad : Array (Name × Expr)
  recuArgMv : Array Expr
  motArgMv : Array Expr
  motMv : Expr
deriving Inhabited, Repr, BEq

structure FunRecursorCache extends RecursorCache where
  targets : List Nat
  argNum : Nat
deriving Inhabited, Repr, BEq



def processRecursorCache (recu : Name) : MetaM RecursorCache := do
  match (← getEnv).find? recu with
  | .some info =>
      let (lvl,lcache) ← mkFreshTaggedLevelMVarsForWN "processRecursorCache" info
      let R := Expr.const recu lvl
      let T ← inferType R
      let (recA,_,g) ← ForallMetaTagTelescope (← getLCtx) (← getLocalInstances) "processRecursorCache" T
      let motA := g.getAppArgs
      let mot := g.getAppFn
      let mut ecache : Array (Name × Expr) := Array.replicate recA.size (.anonymous, failExpr "processRecursorForCache")
      let mut i := 0
      for e in recA do
        let mv := e.mvarId!
        let T ← mv.getType
        ecache := ecache.set! i (mv.name,T)
        i := i+1
      match mot with
      | .mvar .. =>
        if motA.any (fun | .mvar .. => false | _ => true)
        then
          throwError s!"[processRecursorForCache] unsupported format '{recu}'"
        else
          return ⟨recu,R,lcache,ecache,recA,motA, mot⟩
      | _ => throwError s!"[processRecursorForCache] unsupported format '{recu}'"
  | .none      => throwError s!"[processRecursorForCache] '{recu}' not in environment "


def loadRecursorCache (l1 : LocalContext) (l2 : LocalInstances) (recu : RecursorCache) : MetaM Unit := do
  loadLMVarsNoCoA recu.lvlLoad
  loadMVarsWiCoA recu.argLoad l1 l2

def loadFunRecursorCache (l1 : LocalContext) (l2 : LocalInstances) (recu : FunRecursorCache) : MetaM Unit := do
  loadRecursorCache l1 l2 recu.toRecursorCache
