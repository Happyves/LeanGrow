

/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Caching.Score.Query
import LeanGrow.Src.Utils.Lean.TestTools

open Lean Meta


unsafe def q_thm (mod : Name) (back? : Bool) (thmName : Name) : Array Expr → Array Expr → MetaM Unit
  | fvs, objs => do
    let goal := objs[0]!
    let mut ltx := PaIn.dead
    let mut i := 0
    for fv in fvs do
      let T ← inferType fv
      ltx := (← ltx.insert (← getLCtx) (← getLocalInstances) T i UInt32Array.empty
        (fun x => .single x.toUInt32) (fun x y => y.oInsert x.toUInt32)).1
      i := i+1
    query_thm_main
      mod back? goal ltx thmName

#check 1


unsafe def q_gh (mod : Name) (back? : Bool) : Array Expr → Array Expr → MetaM Unit
  | fvs, objs => do
    let goal := objs[0]!
    let mut ltx := PaIn.dead
    let mut i := 0
    for fv in fvs do
      let T ← inferType fv
      ltx := (← ltx.insert (← getLCtx) (← getLocalInstances) T i UInt32Array.empty
        (fun x => .single x.toUInt32) (fun x y => y.oInsert x.toUInt32)).1
      i := i+1
    query_gh_main
      mod back? goal ltx

#check 1

unsafe def test1 := q_thm `LeanGrow.Src.Caching.Score.Test.DummySamples true `List.getElem?_eq_getElem

open List
-- With context (α : Type) (inst1 : BEq α) (a : α) (b : α) (inst2 : LawfulBEq α) (l : List α) (i : Nat) (h : i < l.length) and objects (Option.some (l.replace a b)[i]? = .some (if (l[i] == a) = true then if a ∈ take i l then a else b else l[i])) run test1
