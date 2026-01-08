
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrowBeta.Caching.Build



import Lean

open Lean Meta

variable {IdxCollType : Type _}



@[specialize, inline]
unsafe def inSandbox [Repr IdxCollType]
  (toList : IdxCollType → List Nat)
  (insertMulti intersect union difference : IdxCollType → IdxCollType → IdxCollType)
  (emptyCol : IdxCollType) (empty? : IdxCollType → Bool) (size : IdxCollType → Nat)
  (singleton : Nat → IdxCollType) (insert : Nat → IdxCollType → IdxCollType)
  (thms : Array Name)
  (act : ModuleCacheState IdxCollType → MetaM Unit)
  : MetaM Unit := do
  let env ← getEnv
  let cinfos? := thms.map (fun x => env.find? x)
  let mut i := 0
  for info? in cinfos? do
    if info?.isNone
    then
      throwError s!"[inSandbox] didn't find {thms[i]!}"
    else
      i := i+1
  let cinfos := cinfos?.reduceOption
  let x ← buildCachDataForCore  emptyCol singleton insert
              `Sandbox cinfos
              0 cinfos.size
              .dead #[] .dead 0 .nil #[] .dead 0 .empty .empty
  let thmData : CTrie (Array ThmFormat) :=
    CTrie.insert .empty ((`Sandbox  : Name).toString.toUTF8) x.thm_data
  let hypIndToThm : Nat → ThmFormat := (fun n =>
    let thmIdx := x.stdForwSetTrie_idxToThmIdx[n]!
    x.thm_data[thmIdx]!)
  let res ← SetTrieP.ofList (← getLCtx) (← getLocalInstances) thmData toList hypIndToThm insertMulti intersect union difference emptyCol empty? size x.stdForwSetTrie
  let final : ModuleCacheState IdxCollType :=
    ⟨x.thm_data, x.thmNameToIdx, x.thmNameToHypIdx, x.stdBackPaIn, res, x.stdForwSetTrie_idxToThmIdx, x.rwBackPaIn, x.rwForwPaIn⟩
  act final


@[specialize]
unsafe def inSandboxS
  (thms : Array Name)
  (act : ModuleCacheState (List Nat) → MetaM Unit)
  : MetaM Unit :=
  inSandbox
    id (fun x y => x.foldl (fun R a => (R.orderedInsertOrLeave a)) y) (List.orderedIntersect)
    (List.orderedUnion) (List.orderedDiff) [] List.isEmpty List.length
    (fun x => [x]) ((List.orderedInsertOrLeave))
    thms
    act
