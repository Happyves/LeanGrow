

import LeanGrow.F.Utils.Trie.Sorted

open Lean


inductive sCTrie (α : Type) where
  | leaf : Option α → sCTrie α
  | node1 : Option α → ByteArray → sCTrie α → sCTrie α
  | node : Option α → Array ByteArray → Array (sCTrie α) → sCTrie α
  | pointer (_ : Nat)
deriving Repr, BEq, Inhabited
