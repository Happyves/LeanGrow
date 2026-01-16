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

import Mathlib.Data.List.Dedup


open Lean Meta PaIn

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


open List
#check List.Perm

tracing_mode .std
tracing_flags [(`PaIn.uniFEwBTCore, TracingFlags.all),
                (`PaIn.queryLCore.go, TracingFlags.all),
              ]

set_option linter.style.longLine false

With gnodes (l : List Nat) (L : List Nat) and unodes and tnodes and lnodes and objects (List.Perm l.dedup.dedup L.dedup), (List.Perm (42 :: l).dedup L.dedup), (List.Perm l.dedup.dedup L.dedup) run testFB


#check 1

#print PaIn.uniFEwBTCore
