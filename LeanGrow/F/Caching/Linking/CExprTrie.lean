
import LeanGrow.F.Utils.CExprTrie.Types

open Lean


inductive sCTval (α : Type _) where
| ofVal (_ : α)
| ofPoint (_ : Nat)
deriving BEq, Inhabited, Repr

inductive sCExprTrie where
| br  (lnodes : sCTval (List (List Nat × Nat × Option Nat ))) --
      (gnodes : sCTval (List (List Nat × Nat))) --
      (bvars : sCTval (List (List Nat × Nat))) --
      (sorts : sCTval (List (List Nat × Level))) --
      (consts : sCTval (List (List Nat × Name × List Level))) --
      (lits : sCTval (List (List Nat × Literal))) --
      (f : sCExprTrie) (a : sCExprTrie) (appInd : List Nat)
      (f : sCExprTrie) (a : sCExprTrie) (lamInd : List Nat)
      (f : sCExprTrie) (a : sCExprTrie) (allInd : List Nat)
      (f : sCExprTrie) (a : sCExprTrie) (z : sCExprTrie) (letInd : List Nat)
      (projs : sCTval (List (List Nat × Name × Nat × sCExprTrie))) --
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

-/


inductive ListType where
| ln (_ : List (List Nat × Nat × Option Nat))
| num (_ : List (List Nat × Nat))
| so (_ : List (List Nat × Level))
| co (_ : List (List Nat × Name × List Level))
| li (_ : List (List Nat × Literal))
| trie (_ : sCExprTrie)
| pro (_ : List (List Nat × Name × Nat × sCExprTrie))
deriving BEq, Inhabited, Repr


partial def sCExprTrie.stratify (T : CExprTrie) (d w : Nat) : sCExprTrie × List (Nat × ListType) := sorry
  -- currently we need to write code for all 2^7 cases where combinations of lists can have their
  -- length exeed `w`, in which case we'd want to replace them by pointers...

/-
For now we just print the whole CExprTrie, the assumption beeing that they're pretty small anyway,
where we us the measure ↓ for when they're keys in SetTrie.

-/

partial def CExprTrie.measure : CExprTrie → Nat
  | .dead => 0
  | .br lnodes gnodes bvars sorts consts lits apf apa _ laf laa _ alf ala _ lef lea lez _ projs =>
      lnodes.length + gnodes.length + bvars.length + sorts.length + consts.length + lits.length +
        apf.measure + apa.measure + laf.measure + laa.measure + alf.measure + ala.measure + lef.measure + lea.measure + lez.measure +
          ((projs.map (fun x => x.2.2.2.measure)).foldl (fun x y => x+y) 0)
