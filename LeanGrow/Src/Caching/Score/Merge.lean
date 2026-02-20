/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Caching.Score.Types

open Lean Meta


def thmGenDataEntry.merge {IdxCollType : Type _}
  (empty : IdxCollType) (shiftAdd : Nat → IdxCollType → IdxCollType)
  (union : IdxCollType → IdxCollType → IdxCollType)
  (l r : thmGenDataEntry IdxCollType) : thmGenDataEntry IdxCollType :=
    let shif := l.goalWeights.size
    let rp := r.goalPain.mapInds (fun x => shiftAdd shif x) empty
    let goalPain := PaIn.merge union empty l.goalPain rp
    let goalWeights := l.goalWeights ++ r.goalWeights
    let goalTotal := l.goalTotal + r.goalTotal
    let hypTotal := l.hypTotal + r.hypTotal
    let hypSetTrie :=  l.hypSetTrie



#check SetTrieP.mergeNoJoin
#check SetTrieP.map

/-
Todo:
merge of settries should make sure indices are disjoint ...

-/
