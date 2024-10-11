

import LeanGrow.F.Data.Unification.EmbedGoal



def NodeExpr.toCExpr : NodeExpr → CExpr
|  .ofLNode i =>  .lnode i (.ofBvar 42)
|  .ofGNode i =>  .gnode i (.ofBvar 42)
|  .ofCExpr ce => ce


/-- returns unassigned hyps of applied thm, together with their typ, where local dependent lnodes are replaced
by gnodes from the query-ltx that were derived from unification -/
def propagate_gnode_to_lnode (thm_data : Array EmbedData)
  (matchData : Array (Option NodeExpr)) : List Nat × List (Nat × CExpr) :=
  let (assigned, toFix) : List (Nat × CExpr) × List (Nat × CExpr) :=
    (matchData.foldl
    (fun (i,a,f) as? =>
        match as? with
        | .some ne => (i+1, (i, NodeExpr.toCExpr ne) :: a, f)
        | _ => (i+1, a, (i, (thm_data.get! i).cexpr) :: f)
    )
    (0,[],[])).2
  let rec update : CExpr → CExpr
    | .lnode i o =>
          match assigned.find? (fun x => x.1 == i) with
          | .some ce => ce.2
          | _ => .lnode i o
    | .app f a => .app (update f) (update a)
    | .lam n f a i => .lam n (update f) (update a) i
    | .forallE n f a i => .forallE n (update f) (update a) i
    | .letE n f a z i => .letE n (update f) (update a) (update z) i
    | .proj n i a => .proj n i (update a)
    | ce => ce
  let fixed := toFix.map (fun (i,ce) => (i, update ce))
  (assigned.map Prod.fst, fixed)
