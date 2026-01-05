
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanDejaVue.Data.PathIndex.Insert
import LeanDejaVue.Utils.Lean.TestTools


open Lean Meta PaIn


def testInsert : Array Expr → Array Expr → Array Expr → MetaM Unit
  | Gnodes, Tnodes, Objs => do
      let mut L := []
      let mut i := 0
      for O in Objs do
        L := (i,O) :: L
        i := i+1
      let ⟨T,l1,l2⟩ ← PaIn.ofList (← getLCtx) (← getLocalInstances) L .dead [] (fun x => [x])
        List.orderedInsertOrLeave
      withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
        let built := (T.buildCore [] 0 id List.orderedIntersect List.isEmpty).toListOfProd
        IO.println s!"{built}"
        let built := ← built.mapM (fun (x,y) => return (← ppExpr x, y))
        IO.println s!"{built}"
        IO.println s!"{repr T}"



#check 1

With context (n : Nat) (m : Nat) and mvars and objects (n+m), (n-m), (n*m), (fun x : Nat => ∀ y : Nat, x = y), (fun x : Nat => ∀ y : Nat, x = y+1) run testInsert

#check 1

With context (n : Nat) (m : Nat) (x : Fin (n+m)) (P : (k : Nat) → Fin k → Prop) {y : Fin (n+m) : x+x} and mvars and objects (P (n+m) y), (∃ f : Nat → Nat, f = fun x : Nat => x), (∀ y : Fin (n+m), y = x), (let z : Fin (n+m) := y ; P (n+m) z) run testInsert

#check 1

With context (m : Nat × Nat) (n : Nat) (x : Fin n) {y : Fin (n+1) : Fin.mk 0 (Nat.zero_lt_succ n)} and mvars (z : Fin (n+1)) and objects (m.1 = m.2), (y + ⟨x.val, Nat.lt_trans x.isLt (Nat.lt_succ_self n)⟩ = ?z) run testInsert

#check Nat.lt_succ_self
#check Nat.zero_lt_succ
#print Fin
#check Nat.lt_trans
