
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Utils.Std.List


inductive SetTrie (α β : Type _)  where
| root (c : List (SetTrie α β))
| node (q : β) (c : List (SetTrie α β))
| leaf (a : α)
deriving Inhabited, Repr, BEq

inductive SetTrieP (α : Type _) (IdxCollType : Type u) (PaIn : Type u → Type u)  where
| root (q : PaIn IdxCollType) (c : Array (SetTrieP α IdxCollType PaIn))
| node (k : IdxCollType) (q : PaIn IdxCollType) (c : Array (SetTrieP α IdxCollType PaIn))
| leaf (a : α)
deriving Inhabited
