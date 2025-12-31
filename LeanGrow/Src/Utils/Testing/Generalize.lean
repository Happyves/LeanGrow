

/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrowBeta.Utils.Lean.TestTools
import LeanGrowBeta.Utils.Lean.Generalize


open Lean Meta



def test1 : Array Expr → Array Expr → MetaM Unit :=
  (fun _ os => do
    let T := os[0]!
    let (gt,_) ← generalizeProofs (← getLCtx) (← getLocalInstances) T
    IO.println (← ppExpr gt)
    )

With context (l : List Nat) (x : Nat) and objects ((x :: l).reverse).get  ⟨l.length, (by rw [List.length_reverse] ; dsimp ; exact Nat.lt.base (List.length l)) ⟩ run test1
