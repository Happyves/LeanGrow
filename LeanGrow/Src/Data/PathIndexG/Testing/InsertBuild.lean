
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Data.PathIndexG.Insert
import LeanGrow.Src.Utils.LeanGrow.TestTools


open Lean Meta PaInG


def testInsert : Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array DepCache → Array (FVarId × List FVarId) → MetaM Unit
  | _,Gnodes, _,_, _, _, _, _, _, _, Objs, _, _ => do
      let mut L := []
      let mut i := 0
      for O in Objs do
        L := (i,O) :: L
        i := i+1
      let ⟨T,l1,l2⟩ ← PaInG.ofList (← getLCtx) (← getLocalInstances) L .dead UInt32Array.empty (fun x => UInt32Array.single x.toUInt32)
        (fun x y => UInt32Array.oInsert y x.toUInt32)
      withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
        let built := (T.buildCore [] 0 id UInt32Array.inter UInt32Array.isEmpty).toListOfProd
        IO.println s!"{built}"
        let built := ← built.mapM (fun (x,y) => return (← ppExpr x, y))
        IO.println s!"{built}"
        IO.println s!"{repr T}"



#check 1

With context g(n : Nat) g(m : Nat) and objects (n+m), (n-m), (n*m), (fun x : Nat => ∀ y : Nat, x = y), (fun x : Nat => ∀ y : Nat, x = y+1) run testInsert

#check 1

With context g(n : Nat) g(m : Nat) g(x : Fin (n+m)) g(P : (k : Nat) → Fin k → Prop) u(y : Fin (n+m) : x+x) and objects (P (n+m) y), (∃ f : Nat → Nat, f = fun x : Nat => x), (∀ y : Fin (n+m), y = x), (let z : Fin (n+m) := y ; P (n+m) z) run testInsert

#check 1

With context g(m : Nat × Nat) g(n : Nat) g(x : Fin n) u(y : Fin (n+1) : Fin.mk 0 (Nat.zero_lt_succ n)) t(0 : 0 : z : Fin (n+1)) and objects (m.1 = m.2), (y + ⟨x.val, Nat.lt_trans x.isLt (Nat.lt_succ_self n)⟩ = z) run testInsert

#check Nat.lt_succ_self
#check Nat.zero_lt_succ
#print Fin
#check Nat.lt_trans
