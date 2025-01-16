
import LeanGrow.F.Data.CExpr.Types
import Lean

open Lean

inductive SampleActionType where -- sync with Ranking.WithStats.Types
| ofF | ofB | ofFrw | ofBrw | ofOther
deriving Inhabited, Repr, BEq


structure SampleTypeRaw where
  kind : SampleActionType
  thmName : Name
  goal : CExpr
  -- ↑↓ should be in terms of lnodes, in accordance to CExprTrie.contains to make queries work
  ltx : List (Nat × CExpr)
deriving Inhabited, Repr, BEq

structure preSampleTypeRaw where
  kind : SampleActionType
  thmName : Name
  goal : Expr
  ltx : List (Expr)
  Ltx : LocalContext
deriving Inhabited--, Repr, BEq
