
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Data.CTrie.Operations


open Lean Meta

inductive PaIn (IdxCollType : Type _) where
| br  (fvars mvars :  CTrie (IdxCollType))
      (bvars: ListProd IdxCollType Nat)
      (sorts : ListProd IdxCollType Level)
      (consts : CTrie (ListProd IdxCollType (List Level)))
      (lits : ListProd IdxCollType Literal)
      (f : PaIn IdxCollType) (a : PaIn IdxCollType) (appInd : IdxCollType)
      (f : PaIn IdxCollType) (a : PaIn IdxCollType) (lamInd : IdxCollType)
      (f : PaIn IdxCollType) (a : PaIn IdxCollType) (allInd : IdxCollType)
      (f : PaIn IdxCollType) (a : PaIn IdxCollType) (z : PaIn IdxCollType) (letInd : IdxCollType)
      (projs : CTrie (ListProd IdxCollType (Nat × PaIn IdxCollType)))
      (proofsOf : PaIn IdxCollType) (proofs : PaIn IdxCollType)
| dead
deriving BEq, Inhabited, Repr


abbrev PaInS := PaIn (List Nat)
