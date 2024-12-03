
import LeanGrow.F.Utils.CExprTrie.Types

open Lean


inductive sCExprTrie where
| br  (lnodes : Nat) -- List (List Nat × Nat × Option Nat )
      (gnodes : Nat) -- List (List Nat × Nat)
      (bvars : Nat) -- List (List Nat × Nat)
      (sorts : Nat) -- List (List Nat × Level)
      (consts : Nat) -- List (List Nat × Name × List Level)
      (lits : Nat) -- List (List Nat × Literal)
      (f : sCExprTrie) (a : sCExprTrie) (appInd : List Nat)
      (f : sCExprTrie) (a : sCExprTrie) (lamInd : List Nat)
      (f : sCExprTrie) (a : sCExprTrie) (allInd : List Nat)
      (f : sCExprTrie) (a : sCExprTrie) (z : sCExprTrie) (letInd : List Nat)
      (projs : Nat) -- List ( List Nat × Name × Nat × sCExprTrie)
| dead
| pointer (_ : Nat)
deriving BEq, Inhabited, Repr

#check 1

/-
TODO:

- For SetTrie, write function that prints from list of keys and tries, in the right

- For sCExprTrie, use common counter for lnode.-like data, trees, and projs-data.
  We must do this to make sure that the trees in the proj lists will be printed
  before the proj lists are printed, which should in turn be printed before the tree
  its a part of

- possily replace pointer for lists by option type with either a pointer or a lists,
  so that small lists get directly printed ?

-/
