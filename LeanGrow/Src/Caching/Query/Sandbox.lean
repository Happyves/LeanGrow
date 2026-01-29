
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Caching.Query.Build



import Lean

open Lean Meta

variable {IdxCollType : Type _}



@[specialize, inline]
def inSandbox [Repr IdxCollType]
  (intersect union difference : IdxCollType → IdxCollType → IdxCollType)
  (emptyCol : IdxCollType) (empty? : IdxCollType → Bool) (size : IdxCollType → Nat)
  (singleton : Nat → IdxCollType) (insert : Nat → IdxCollType → IdxCollType)
  (thms : Array Name)
  (act : CTrie (Array ThmFormat) → ModuleCacheState IdxCollType → MetaM Unit)
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
              .dead #[] .dead 0 .nil #[] #[] .dead 0 .empty .empty
  let thmData : CTrie (Array ThmFormat) :=
    CTrie.insert .empty ((`Sandbox  : Name).toString.toUTF8) x.thm_data
  let res ← SetTriePGSpe.ofList thmData intersect union difference emptyCol empty? size x.stdForwSetTrie
  let final : ModuleCacheState IdxCollType :=
    ⟨x.thm_data, x.thmNameToIdx, x.thmNameToHypIdx, x.stdBackPaIn, res, x.stdForwSetTrie_idxToThmIdx, x.stdForwSetTrie_idxToSinkIdx, x.rwBackPaIn, x.rwForwPaIn⟩
  act thmData final


@[specialize, inline]
def inSandboxS
  (thms : Array Name)
  (act : CTrie (Array ThmFormat) → ModuleCacheState UInt32Array → MetaM Unit)
  : MetaM Unit :=
  inSandbox
    UInt32Array.inter UInt32Array.union UInt32Array.diff
    UInt32Array.empty UInt32Array.isEmpty UInt32Array.size
    (fun x => UInt32Array.single x.toUInt32) (fun x y => y.oInsert x.toUInt32)
    thms
    act
