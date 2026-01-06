/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Data.SetTrie.Build


instance {α : Type _} [I : Inhabited α] (IdxCollType : Type u) (PaIn : Type u → Type u) : Inhabited (SetTrieP α IdxCollType PaIn) where
  default := .leaf I.default


@[inline, specialize]
partial def SetTrieP.mk
  {α : Type _} [Inhabited α]
  (IdxCollType : Type u)
  (PaIn : Type u → Type u)
  (merge : (PaIn IdxCollType) → (PaIn IdxCollType) → (PaIn IdxCollType)) (empty : (PaIn IdxCollType))
  (getInds : (PaIn IdxCollType) → IdxCollType)
  (T : SetTrie α (PaIn IdxCollType)) : SetTrieP α IdxCollType PaIn :=
  let rec @[specialize] go [Inhabited α] : SetTrie α (PaIn IdxCollType) → SetTrieP α IdxCollType PaIn
    | .root c =>
        let K := c.foldOnKeys empty merge
        .root K (c.toArray.map go)
    | .node q c =>
        let is := getInds q
        let K := c.foldOnKeys empty merge
        .node is K (c.toArray.map go)
    | .leaf v => .leaf v
  go T
