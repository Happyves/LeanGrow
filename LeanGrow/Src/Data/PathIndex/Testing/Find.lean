
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanDejaVue.Data.PathIndex.Find
import LeanDejaVue.Data.PathIndex.Indexing
import LeanDejaVue.Data.PathIndex.Insert
import LeanDejaVue.Utils.Lean.TestTools


open Lean Meta PaIn


def testInsert : Array Expr → Array Expr → Array Expr → MetaM Unit
  | Fvs, _, Objs => do
      let mut L := []
      let mut i := 0
      for O in Objs do
        L := (i,O) :: L
        i := i+1
      let ⟨T,l1,l2⟩ ← PaIn.ofList (← getLCtx) (← getLocalInstances) L .dead [] (fun x => [x])
        List.orderedInsertOrLeave
      IO.println s!"{← T.ppS l1 l2 [] 0}\n"
      let allInd := T.getIndicesS
      IO.println s!"{allInd}\n"
      let ⟨qase,res1,_,l1,l2⟩ ← T.findS l1 l2 allInd 2 Objs[0]!
      if qase == 0
      then (IO.println "misc fail 1")
      else if qase == 1
      then (IO.println "dead fail 1")
      else if qase == 2
      then (IO.println "naive fail 1")
      else
        IO.println s!"res1 : {res1}\n"
        let ⟨qase,res1,_,l1,l2⟩ ← T.findS l1 l2 allInd 2 (← inferType Fvs[4]!)
        if qase == 0
        then (IO.println "misc fail 1")
        else if qase == 1
        then (IO.println "dead fail 1")
        else if qase == 2
        then (IO.println "naive fail 1")
        else
          IO.println s!"res1 : {res1}\n"

With context (n : Nat) (m : Nat) (x : Fin (n+m)) (P : (k : Nat) → Fin k → Prop) (h : P (n+m) x) {y : Fin (n+m) : x+x} and mvars and objects (P (n+m) y), (∃ f : Nat → Nat, f = fun x : Nat => x), (∀ y : Fin (n+m), y = x), (let z : Fin (n+m) := y ; P (n+m) z) run testInsert



#check 1

def testFindeDefEq : Array Expr → Array Expr → Array Expr → MetaM Unit
  | Gnodes, _, Objs => do
      let ⟨T,l1,l2⟩ ← PaIn.ofList (← getLCtx) (← getLocalInstances) [(0, Objs[0]!)] .dead [] (fun x => [x])
        List.orderedInsertOrLeave
      IO.println s!"{← T.ppS l1 l2 [] 0}\n"
      let allInd := T.getIndicesS
      IO.println s!"{allInd}\n"
      let ⟨qase,res1,_,l1,l2⟩ ← T.findS l1 l2 allInd 2 Objs[1]!
      if qase == 0
      then (IO.println "misc fail 1")
      else if qase == 1
      then (IO.println "dead fail 1")
      else if qase == 2
      then (IO.println "naive fail 1")
      else
        IO.println s!"res1 : {res1}\n"
        let ⟨T,l1,l2⟩ ← PaIn.ofList (← getLCtx) (← getLocalInstances) [(0, Objs[1]!)] .dead [] (fun x => [x])
          List.orderedInsertOrLeave
        IO.println s!"{← T.ppS l1 l2 [] 0}\n"
        let allInd := T.getIndicesS
        IO.println s!"{allInd}\n"
        let ⟨qase,res1,_,l1,l2⟩ ← T.findS l1 l2 allInd 2 Objs[0]!
        if qase == 0
        then (IO.println "misc fail 1")
        else if qase == 1
        then (IO.println "dead fail 1")
        else if qase == 2
        then (IO.println "naive fail 1")
        else
          IO.println s!"res1 : {res1}\n"


With context (n : Nat) (m : Nat) and mvars and objects (42 = Nat.succ (Nat.add n m)), (42 = Nat.add n m.succ) run testFindeDefEq

With context (n : Nat) (m : Nat) and mvars and objects (Nat.succ (Nat.add n m) = 42), (Nat.add n m.succ = 42) run testFindeDefEq
