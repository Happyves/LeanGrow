

import LeanGrow.F.Search.A.trTypes
import LeanGrow.F.Utils.Array
import LeanGrow.F.Data.CExpr.API

open Lean

/-
Backsteps should delete one goal, and possibly (probably) add new goals.
Unisteps should delete goals.
If there are no active goals, then we may assemble.
-/


partial def BackTree.assemble : BackTree → CExpr
  | .fail => .failed
  | .ofGoal _ _ => .failed
  | .ofAssign ce => ce
  | .ofBack _ n _ _ args =>
        let mk := args.mapF BackTree.assemble
        CExpr.mkAppA (.const n []) mk -- fix levels
