
import LeanGrow.F.Utils.ExprTrie.Types
import LeanGrow.F.Utils.List
import LeanGrow.F.Utils.Tracing

open Lean


partial def CExprTrie.match_candidates? [BEq α] (T : CExprTrie α) (ce : CExpr) (r : α → α → Prop) [DecidableRel r] : List (List α) :=
    let rec go
