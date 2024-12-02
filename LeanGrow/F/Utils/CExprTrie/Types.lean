
import LeanGrow.F.Data.CExpr.Types


open Lean


inductive CExprTrie where
| br  (lnodes : List (List Nat × Nat × Option Nat ))
      (gnodes : List (List Nat × Nat))
      (bvars : List (List Nat × Nat))
      (sorts : List (List Nat × Level))
      (consts : List (List Nat × Name × List Level)) -- Trie ?
      (lits : List (List Nat × Literal))
      (f : CExprTrie) (a : CExprTrie) (appInd : List Nat)
      (f : CExprTrie) (a : CExprTrie) (lamInd : List Nat)
      (f : CExprTrie) (a : CExprTrie) (allInd : List Nat)
      (f : CExprTrie) (a : CExprTrie) (z : CExprTrie) (letInd : List Nat)
      (projs : List ( List Nat × Name × Nat × CExprTrie))
| dead
deriving BEq, Inhabited, Repr


inductive oDirs where
| apf | apa | laf | laa | alf | ala | lef | lea | lez | pro
deriving BEq, Inhabited, Repr
