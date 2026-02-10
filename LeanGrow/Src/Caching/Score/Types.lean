
/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.SampleGenScore.Gen.ConjecturableBuild
import LeanGrow.Src.SampleGenScore.Gen.Conveyorbelts
import LeanGrow.Src.SampleGenScore.Gen.Subpattern

open Lean Meta


structure ProcessedSamplesThmKey (IdxCollType : Type _) where
  sampleName : Name
  regularBack : CTrie (Prod5 Nat Nat (ListProd Nat (List Nat)) (PaIn IdxCollType) (PaIn IdxCollType))
  regularForw : CTrie (Prod5 Nat Nat (ListProd Nat (List Nat)) (PaIn IdxCollType) (PaIn IdxCollType))
  subpat : CTrie (Nat × PaIn IdxCollType) -- Prod3 Nat (PaIn IdxCollType) (Array ByteArray)
  conj : (CTrie (Prod6 Nat Nat (ListProd Nat (List Nat)) (PaIn IdxCollType) (PaIn IdxCollType) (Array (Nat × PaIn IdxCollType))))
  levelNum : Nat
  types : Array Expr
deriving Inhabited


structure scoreThmKey (IdxCollType : Type _) where
  sampleName : Name
  regularBack : CTrie (thmGenDataEntry IdxCollType)
  regularForw : CTrie (thmGenDataEntry IdxCollType)
  subpat : CTrie (Prod3 (PaIn IdxCollType) (Array Nat) Nat)
  conj : CTrie (Prod3 (thmGenDataEntry IdxCollType) Nat (Array (ListProd ThmFormat Nat)))
  levelNum : Nat
  types : Array Expr
deriving Inhabited



structure ProcessedSamplesGHKey (IdxCollType : Type _) where
  sampleName : Name
  regularBack : Prod3 Nat (PaIn IdxCollType) (Array (Prod4 Nat Nat (ListProd ByteArray (List Nat)) (PaIn IdxCollType)))
  regularForw : Prod3 Nat (PaIn IdxCollType) (Array (Prod4 Nat Nat (ListProd ByteArray (List Nat)) (PaIn IdxCollType)))
  subpat : Prod3 Nat (PaIn IdxCollType) (Array ByteArray)
  conj : (CTrie (Prod6 Nat Nat (ListProd Nat (List Nat)) (PaIn IdxCollType) (PaIn IdxCollType) (Array (Nat × PaIn IdxCollType))))
  levelNum : Nat
  types : Array Expr
deriving Inhabited


structure scoreGHKey (IdxCollType : Type _) where
  sampleName : Name
  regularBack : goalhypGenData IdxCollType
  regularForw : goalhypGenData IdxCollType
  subpatPain : PaIn IdxCollType
  subpatVal : Array (CTrie Nat)
  subpatTotalWeight : Nat
  conj : CTrie (Prod3 (thmGenDataEntry IdxCollType) Nat (Array (ListProd ThmFormat Nat)))
  levelNum : Nat
  types : Array Expr
deriving Inhabited
