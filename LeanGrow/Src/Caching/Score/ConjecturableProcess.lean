
/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Lean.Meta.Basic
import LeanGrow.Src.Utils.Lean.Expr.Basic


open Lean Meta

partial def getConjecturablePos (type : Expr) : MetaM (List Nat) := do
  let rec process (i : Nat) (hyps : Array Expr) (insts : List Nat) (T : Expr) : MetaM (Prod3 Expr (Array Expr) (List Nat)) := do
    match T with
    | .forallE _ t b bi =>
      let t ← withTransparency .reducible <| reduce (skipTypes := false) t
      let t := t.cleanupAnnotations
      let mv ← mkMvarStdNoCoE (.num `dummy i) t
      let b := Expr.instantiate1 b mv
      match bi with
      | .instImplicit =>
        process (i+1) hyps (i :: insts) b
      | _ =>
        process (i+1) (hyps.push t) insts b
    | .letE _ _ v b _ =>
      process i hyps insts (Expr.instantiate1 b v)
    | _ => return .mk T hyps insts
  let .mk goal hyps insts ← process 0 #[] [] type
  let gdeps := goal.onAllSubtermsFold insts (fun e l =>
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
      if !(← isProp T)
      then
        let tdeps := T.onAllSubtermsFold [] (fun e l =>
          match e with
          | .mvar (.mk (.num _ pos)) => l.insert pos
          | _ => l
          )
        res := i :: (res.filter (fun x => !(tdeps.contains x)))
      i := i+1
  return res.mergeSort (· ≤ ·) -- important that sorted !
