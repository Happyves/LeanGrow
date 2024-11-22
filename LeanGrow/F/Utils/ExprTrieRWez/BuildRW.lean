
import LeanGrow.F.Utils.ExprTrieRWez.Unify


#check 1

-- This is where we see that it would be good to add directions to the constructors
-- so that we don't have to search the whole tree.

partial def CExprTrie.factor [BEq α] (T : CExprTrie α) (tidx cidx: Nat)
  (r : α → α → Prop) [DecidableRel r] : CExpr :=
  let rec go (depth : Nat)
