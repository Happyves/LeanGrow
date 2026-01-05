
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Data.CTrie.Operations
import LeanGrow.FFI.Lffi

open Lean Meta

inductive PaInG (IdxCollType : Type _) where
| br  (tnodes : ListProd IdxCollType (Nat × Nat))
      (lnodes :  CTrie (ListProd IdxCollType (Nat × Nat)))
      (gnodes unodes bvars: ListProd IdxCollType Nat)
      (sorts : ListProd IdxCollType Level)
      (consts : CTrie (ListProd IdxCollType (List Level)))
      (lits : ListProd IdxCollType Literal)
      (f : PaInG IdxCollType) (a : PaInG IdxCollType) (appInd : IdxCollType)
      (f : PaInG IdxCollType) (a : PaInG IdxCollType) (lamInd : IdxCollType)
      (f : PaInG IdxCollType) (a : PaInG IdxCollType) (allInd : IdxCollType)
      (f : PaInG IdxCollType) (a : PaInG IdxCollType) (z : PaInG IdxCollType) (letInd : IdxCollType)
      (projs : CTrie (ListProd IdxCollType (Nat × PaInG IdxCollType)))
      (proofsOf : PaInG IdxCollType) (proofs : PaInG IdxCollType)
| dead
deriving BEq, Inhabited, Repr


abbrev PaInGS := PaInG UInt32Array
