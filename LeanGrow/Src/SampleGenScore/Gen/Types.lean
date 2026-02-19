
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Data.PathIndex.Types
import LeanGrow.Src.Data.SetTrie.Specialize


open Lean


@[specialize, inline]
def addCPIweights {IdxCollType : Type _}
  (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β)
  (weights : Array Nat) (start : Nat) (inds : IdxCollType) : Nat :=
    fold inds start (fun i R => R + weights[i]!)

@[specialize, inline]
def getCPIweights {IdxCollType : Type _}
  (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β)
  (weights : Array Nat) (inds : IdxCollType) : Nat :=
    addCPIweights fold weights 0 inds

structure thmGenDataEntry (IdxCollType : Type _) where
  goalPain : PaIn IdxCollType
  goalWeights : Array Nat
  goalTotal : Nat
  hypSetTrie : SetTrieP (Nat × Nat) IdxCollType PaIn
  hypTotal : Nat
deriving Inhabited

instance (IdxCollType : Type _) : EmptyCollection (thmGenDataEntry IdxCollType) where
  emptyCollection := ⟨.dead, #[], 0, .root .dead #[], 0⟩


structure goalhypGenDataEntry (IdxCollType : Type _) where
  hypSetTrie : SetTrieP (CTrie Nat) IdxCollType PaIn
  hypWeights : Array Nat
  hypTotal : Nat
deriving Inhabited

instance (IdxCollType : Type _) : EmptyCollection (goalhypGenDataEntry IdxCollType) where
  emptyCollection := ⟨ .root .dead #[], #[], 0⟩



structure goalhypGenData (IdxCollType : Type _) where
  goalPain : PaIn IdxCollType
  goalWeights : Array Nat
  goalTotal : Nat
  hypEntries : Array (goalhypGenDataEntry IdxCollType)
deriving Inhabited


instance (IdxCollType : Type _) : EmptyCollection (goalhypGenData IdxCollType) where
  emptyCollection := ⟨.dead, #[], 0, #[]⟩
