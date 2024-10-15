

import LeanGrow.F.Data.Unification.EmbedRaw

#check 1


def integrate_forward_raw (forwarIdCounter : Nat) (embed : EmbedStruct) (thm_goal : CExpr) -- should be derived from the second part of `ThmType_ToDAG`
  (ltx_cexprs : List (Nat × CExpr)) (ltx_assembly : List (Nat × EmbedStruct)) :
  (List (Nat × CExpr)) × (List (Nat × EmbedStruct)) :=
  let rec trafo_goal_cexpr : CExpr → CExpr -- to optimize
    | .lnode i o .none =>
        match embed.embed.get! i with
        | .some (.ofGNode j) => .gnode j (.ofBvar 42)
        | _ => sorry -- may happend for example an the Add intance for Nat may be in the goal, but will not be assigned...
    | .app l r => .app (trafo_goal_cexpr l) (trafo_goal_cexpr r)
    | .lam n l r i => .lam n (trafo_goal_cexpr l) (trafo_goal_cexpr r) i
    | .forallE n l r i => .forallE n (trafo_goal_cexpr l) (trafo_goal_cexpr r) i
    | .letE n l r z i => .letE n (trafo_goal_cexpr l) (trafo_goal_cexpr r) (trafo_goal_cexpr z) i
    | .proj n i e => .proj n i (trafo_goal_cexpr e)
    | ce => ce
  let fixed := trafo_goal_cexpr thm_goal
  sorry
