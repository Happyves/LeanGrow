

import LeanGrow.F.Prototypes.MarkSeven.IntroTreeEmbed

#check 1


def integrate_forward_raw (embed : EmbedStruct) (thm_goal : CExpr) -- should be derived from the second part of `ThmType_ToDAG`
  : --(ltx_cexprs : List (Nat × CExpr)) :
  CExpr :=
  let rec trafo_goal_cexpr : CExpr → CExpr -- to optimize
    | .lnode i _ .none =>
        match embed.embed.get! i with
        | .some x => x
        | _ => -- may happend for example an the Add intance for Nat may be in the goal, but will not be assigned...
            .const `ohNo [] -- dummy solution ... will have to find some sort of call to the main procedure to derive instance ?
    | .app l r => .app (trafo_goal_cexpr l) (trafo_goal_cexpr r)
    | .lam n l r i => .lam n (trafo_goal_cexpr l) (trafo_goal_cexpr r) i
    | .forallE n l r i => .forallE n (trafo_goal_cexpr l) (trafo_goal_cexpr r) i
    | .letE n l r z i => .letE n (trafo_goal_cexpr l) (trafo_goal_cexpr r) (trafo_goal_cexpr z) i
    | .proj n i e => .proj n i (trafo_goal_cexpr e)
    | ce => ce
  trafo_goal_cexpr thm_goal
