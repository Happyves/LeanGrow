

#check 1

inductive SetTrie (α : Type _) (β : Type _)  where
| root (c : List (SetTrie α β))
| node (q : β) (c : List (SetTrie α β))
| leaf (a : α)
deriving Inhabited, Repr, BEq
