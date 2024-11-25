

import LeanGrow.F.Utils.ExprTrieRWez.Query


open Lean

-- Could be used to check if any forward-types match backward-goal-types,
-- if the latter are stored in a trie. This should be even more efficient
-- if we impose an order on branches.



partial def CExprTrie.intersect (L R : CExprTrie Nat) : List (List Nat × List Nat) :=
  let rec go :
