
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrowBeta.Core.Embedding.UnifyBEFT
import LeanGrowBeta.Core.Embedding.UnifyFEBT
import LeanGrowBeta.Utils.LeanGrow.TestTools
import LeanGrowBeta.Data.PathIndex.Insert
import LeanGrowBeta.Data.PathIndex.Indexing

open Lean Meta PaIn


def testBF : Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → MetaM Unit
  | Gnodes, Unodes, Tnodes, Lnodes, Objs => do
      let query := Objs[0]!
      let ⟨data,l1,l2⟩ ← PaIn.ofList (← getLCtx) (← getLocalInstances) ((Objs.drop 1).toList.zipIdx.map Prod.swap)
        .dead [] (fun x => [x]) (fun x y => List.orderedInsertOrLeave x y) --(fun x y => List.orderedIntersect x y) List.isEmpty
      let ⟨qase,_,res,_,_⟩ ← uniBEwFTMain
        List.isEmpty (fun x y => List.orderedIntersect x y)  (fun x y => List.orderedUnion x y) (fun x y => List.orderedDiff x y) []
        l1 l2
        (data.getIndices [] (fun x y => List.orderedUnion x y)) 2
        query data
      if qase == 0
      then
        (IO.println "nope 1")
      else if qase == 1
      then
        (IO.println  "nope 2")
      else
        IO.println s!"{toString res}"


With gnodes (n : Nat) (m : Nat) and unodes and tnodes (x : Nat) and lnodes and objects ((fun y : Nat => x + y)), ((fun y : Nat => n + y)), ((fun y : Nat => m + y)), (42 = 42) run testBF

With gnodes (n : Nat) (m : Fin (n+n)) (P : (k : Nat) → Fin (n+k) → Prop) and unodes and tnodes (x : Nat) (y : Fin (n+x)) and lnodes and objects (P x y), ((fun y : Nat => n + y)), (42 = 42), (P n m) run testBF

With gnodes (n : Nat) and unodes and tnodes (x : Nat) and lnodes and objects (fun _ : Nat => x), (fun x : Nat => x), (42 = 42), (fun _ : Nat => 37) run testBF

With gnodes (n : Nat) (m : Nat) and unodes (a : Nat : n+m) (b : Nat : 42) and tnodes (x : Nat) and lnodes and objects (x+b), (n+42), (a+b), (2=2) run testBF

With gnodes (n : Nat) (m : Nat) and unodes (a : Nat : n+m) (b : Nat : 42) and tnodes (x : Nat) (y : Nat) and lnodes and objects (x+(x+y)), (n+42), (n+a), (2=2) run testBF



def testFB : Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → MetaM Unit
  | Gnodes, Unodes, Tnodes, Lnodes, Objs => do
      let query := Objs[0]!
      let ⟨data,l1,l2⟩ ← PaIn.ofList (← getLCtx) (← getLocalInstances) ((Objs.drop 1).toList.zipIdx.map Prod.swap)
        .dead [] (fun x => [x]) (fun x y => List.orderedInsertOrLeave x y) --(fun x y => List.orderedIntersect x y) List.isEmpty
      let ⟨qase,_,res,_,_⟩ ← uniFEwBTMain
        List.isEmpty (fun x y => List.orderedIntersect x y)  (fun x y => List.orderedUnion x y) (fun x y => List.orderedDiff x y) []
        l1 l2
        (data.getIndices [] (fun x y => List.orderedUnion x y)) 2
        query data
      if qase == 0
      then
        (IO.println "nope 1")
      else if qase == 1
      then
        (IO.println  "nope 2")
      else
        IO.println s!"{toString res}"

#check 1

-- tracing_mode .hard
-- tracing_flags [(`PaIn.uniFEwBTCore,TracingFlags.all), (`PaIn.queryLCore.go,TracingFlags.all)]

-- #exit
With gnodes (n : Nat) (m : Nat) and unodes and tnodes (x : Nat) (y : Nat) and lnodes and objects (n+m), (x+y), (y+x), (42 = 42) run testFB

With gnodes (n : Nat) (m : Fin n) (P : (k : Nat) → Fin k → Prop) and unodes and tnodes (x : Nat) (y : Fin x) and lnodes and objects (P n m), (x = 37), (P x y), (42 = 42) run testFB

With gnodes (n : Nat) (m : Fin n) (P : (k : Nat) → Fin k → Prop) and unodes and tnodes (x : Nat) (y : Fin x) and lnodes and objects (P n m), (x = 37), (P x y), (42 = 42) run testFB

With gnodes (n : Nat) (m : Nat) and unodes and tnodes (x : Nat) (y : Nat) and lnodes and objects (n+(m+m)), (x+y), (x +(y+y)), (42 = 42) run testFB

With gnodes (n : Nat) (m : Nat) and unodes and tnodes (x : Nat) (y : Nat) and lnodes and objects (n+(m+m)), (x +(y-y)), (42 = 42) run testFB

With gnodes (n : Nat) (m : Nat) and unodes (k : Nat : n+m) and tnodes (x : Nat) (y : Nat) and lnodes and objects (n+k), (x +(y-y)), (x+y), (x+(x+y)), (42 = 42) run testFB

With gnodes (n : Nat) (m : Nat) (h1 : m = 42) (h2 : 42+n = 37) (h3 : n+m = 37) (P : (k : Nat) → (42+k = 37) → Prop) and unodes and tnodes (x : Nat) (y : 42+x = 37) and lnodes and objects (P n (by rw [Nat.add_comm, ← h1] ; exact h3)), (x = 37), (P n h2), (P x y) run testFB


-- Todo : test unodes, test proofs
