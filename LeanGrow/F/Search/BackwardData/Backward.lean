

import LeanGrow.F.Data.Unification.EmbedGoal
import LeanGrow.F.Search.BackwardData.Types


def NodeExpr.toCExpr : NodeExpr → CExpr
|  .ofLNode i t =>  .lnode i (.ofBvar 42) t
|  .ofGNode i =>  .gnode i (.ofBvar 42)
|  .ofCExpr ce => ce


/-- returns assigned hyps, and unassigned hyps of applied thm, together with their typ,
where local dependent lnodes are replaced
by gnodes from the query-ltx that were derived from unification
Example of le_trans aplication : a and c get assigned, and we should propagate
this to the types of the hypotheses a ≤ b and b ≤ c
-/
def propagate_lnode_and_tag (thm_data : Array EmbedData) (backwardId : Nat)
  (matchData : Array (Option NodeExpr)) : List (Nat × CExpr) × List (Nat × CExpr) :=
  let (assigned, toFix) : List (Nat × CExpr) × List (Nat × CExpr) :=
    (matchData.foldl
    (fun (i,a,f) as? =>
        match as? with
        | .some ne => (i+1, (i, NodeExpr.toCExpr ne) :: a, f)
            -- may produce large terms when lnode was matched to a big expression
        | _ => (i+1, a, (i, (thm_data.get! i).cexpr) :: f)
    )
    (0,[],[])).2
  let rec update : CExpr → CExpr
    | .lnode i o .none => -- important to ignore taged ones, as they are to be considered constants
          match assigned.find? (fun x => x.1 == i) with
          | .some ce => ce.2
          | _ => .lnode i o (.some backwardId)
    | .app f a => .app (update f) (update a)
    | .lam n f a i => .lam n (update f) (update a) i
    | .forallE n f a i => .forallE n (update f) (update a) i
    | .letE n f a z i => .letE n (update f) (update a) (update z) i
    | .proj n i a => .proj n i (update a)
    | ce => ce
  let fixed := toFix.map (fun (i,ce) => (i, update ce))
  (assigned, fixed)


#check 1

/-
Situation:
- first application of le_trans to .gnode a ≤ .gnode c
- new goals .gnode a ≤ .lnode b & .lnode b ≤ .gnode c
- second application of le_trans to .gnode a ≤ .lnode b
- one of the new goals would be .lnode b ≤ .lnode d with indices
  now being meanigless, as we didn't track the thm application
  they refer to.

Idea:
- keep track of numbered goals and backward steps separately:
  for example, initial goal a ≤ b is labeled 0 ; get thm application
  of le_trans labeled 0 which generates 3 new goals to be labeled from
  1 to 3 ; store this info a backwrd-step-label 0 ; change the lnodes
  of the goal types of new goal 1 to 3 at their tag field, to
  notify that they're in the context of backward-step 0 ;
  assume le_trans is applied to goal 3, in a backward-step we label 1 ;
  it creates goals labeled 4 to 6 ; in the lnodes - it would be good
  to have as default tag .none - change those lnodes with the default
  tag to .some 1, so wrt. the backward-step

-/

def integrate_backward_outcome (goalIdCounter backStepIdCounter : Nat)
  (assigned nextGoals: List (Nat × CExpr)) :
  BackStepData × List GoalData × Nat :=
  let gd :=
    nextGoals.foldl
      (fun (L,c) (n,ce) =>
          (⟨c, backStepIdCounter, n, ce⟩ :: L,c+1)
      )
      ([], goalIdCounter)
  (⟨backStepIdCounter, assigned, sorry ⟩,gd)
