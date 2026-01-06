/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Data.SetTrie.Types


@[inline, specialize]
partial def SetTrieP.mk
  {α : Type _} (IdxCollType : Type u) (PaIn : Type u → Type u) [Inhabited (PaIn IdxCollType)]
  (merge : (PaIn IdxCollType) → (PaIn IdxCollType) → (PaIn IdxCollType)) (empty : (PaIn IdxCollType))
  (getInds : (PaIn IdxCollType) → IdxCollType)
  (T : SetTrie α (PaIn IdxCollType)) : SetTrieP α IdxCollType PaIn :=
  let rec @[specialize] go : SetTrie α (PaIn IdxCollType) → (PaIn IdxCollType) × SetTrieP α IdxCollType PaIn
    | .root c =>
        let (k,nc) := c.foldl (fun (k,nc) q =>
          match q with
          | .root .. => panic! "SetTrieP.mk"
          | .node key cs =>
              let ids := getInds key
              let k := merge k key
              let (kcs, ncs) := cs.foldl (fun (K,C) c =>
                let (k,nc) := go c
                let K := merge K k
                (K, nc :: C)) (empty, [])
              (k, (SetTrieP.node ids kcs ncs.toArray) :: nc)
          | .leaf v => (k, (.leaf v) :: nc)
          ) (empty,[])
        (k, .root k nc.toArray)
    |
    | _ => sorry
  sorry
