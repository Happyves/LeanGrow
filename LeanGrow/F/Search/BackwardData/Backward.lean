

import LeanGrow.F.Data.Unification.UnifyForBack
import LeanGrow.F.Search.BackwardData.Types
import LeanGrow.F.Utils.Array

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


partial def compute_subgoal_deps (e : CExpr) : List (Nat × Nat) :=
  let rec go (cache : List (Nat × Nat)) : List CExpr → List (Nat × Nat) -- (appli-tag, thm-idx)
    | [] => cache
    | nx :: more =>
        match nx with
        | .lnode i _ (.some tag) => go ((tag, i) :: cache) more
        | .app l r => go cache (l :: r :: more)
        | .lam _ l r _ => go cache (l :: r :: more)
        | .forallE _ l r _ => go cache (l :: r :: more)
        | .letE _ l r z _ => go cache (l :: r :: z :: more)
        | .proj _ _ r => go cache (r :: more)
        | _ => go cache more
  go [] [e]



def List.Icc (n m : Nat) :=
  let rec go (cache : List Nat) : Nat → List Nat
    | 0 => cache
    | k+1 => go ((k+n) :: cache) k
  go [] (m - n + 1)

def integrate_backward_outcome (goalIdCounter backStepIdCounter : Nat)
  (thm_data : Array EmbedData)
  (assigned nextGoals: List (Nat × CExpr)) :
  BackStepData × List GoalData × Nat :=
  let gd :=
    nextGoals.foldl
      (fun (L,c) (n,ce) =>
          (⟨c, backStepIdCounter, n, ce, compute_subgoal_deps ce⟩ :: L,c+1)
      )
      ([], goalIdCounter)
  (⟨backStepIdCounter, `dummy, thm_data, 42, assigned, List.Icc goalIdCounter gd.2⟩,gd)
  -- replace dummy and 42 by thm name or other assembly data and tageted goal repsctively


#check 1


/-
A goal is solved, if we :
- have a forward type (containing only gnodes), that unifies with the goal,
  in the sense where all (!) lnodes are considered for unification!
  **Important**: make unification version that unify with all .lnodes :
  current ones only unify with .lnode _ .none ?!?
- The solution of one goal implies that of another, of the firsts type
  depended on the seconds, and unification succesfully assigned it


Assume that a goal is solved. We have to:
- propagate solutions ; here we should be careful ... it may theoretically be possible that
  multiple forward type can serve as solution for the same goal. At propagation,
  we should store the fact that the solution by propagation depends on the choice
  of using another solution!
  Ex: for an application of le_trans, we solved 1 ≤ .lnode b t with 1 ≤ 2
    → for thm-appli t, node b should gain solution 2
  Ex multiple sol: goal `L.get? n = .none` and we derived `L.get? 37 = .none`
    and `L.get? 42 = .none` ; yields two different propagation solutions for `n`
- propagate assignements ; other goals may have depended on the one we just solved
  Ex: for an application of le_trans, we solved 1 ≤ .lnode b t with 1 ≤ 2
    → for goal .lnode b ≤ 3, we should spawn the new goal 2 ≤ 3


Solutions:
- To correctly propagate, we should reinstore storing the children in the
  EmbedData, so that propagations as in le_trans are easier to perform
- maybe use a spearate and new tag for solutions and goals ; tag should be a
  Nat. For example, if we solved the goal 1 ≤ .lnode b by le_trans with 1 ≤ 2,
  a solution we store with the tage (counter) 37. the the solution 2 for goal
  Nat corresponding to .lnode b should be taged 37 ; also, the new goal 2 ≤ 3
  (other goal of le_trans) should be tagged 37 → note that we must now have
  a system that understands the the goal shown with le_trans is proven,
  if  the new goal is proven, and not the initial corresponding goal .lnode b ≤ 3,
  which is still open and could get solutions which assigne other vals to .lnode b

-/



/-
**Actually**
Since a subgoal can have lnodes in its type that refer to previous subgoals,
we should think of the backstep as applying to *multiple* different goals. (or not, read ahead)
For example, we could have a first appli of le_trans yielding goals Nat,
1 ≤ .lnode 1 0 and .lnode 1 0 ≤ 4.  We then apply a second le_trans to the second
subgoal, so as to get new goals Nat, 1 ≤ .lnode 1 1 and .lnode 1 1 ≤ .lnode 1 0.
If we have `p : 2 ≤ 3` in the context, and we unify it with .lnode 1 1 ≤ .lnode 1 0, then we should
produce a backstep that has the following data : it solves the initial goal,
produces new subgoals 1 ≤ 2 and 3 ≤ 4, and assigns solutions 2 3 and p.
-/


-- def integrate_solve_outcome
--   (goalIdCounter solveStepIdCounter : Nat)
--   (sol_ltx_id : Nat) (sol_type : CExpr) (goal_data : GoalData)
--   (unif_outcome : List (Nat × (Nat × Nat))) -- from CExpr.MatchAssignSolutions
--   (goal_dict : List (Nat × GoalData))
--   (backStep_dict : List (Nat × BackStepData))
--   (solveStep_dict : List (Nat × SolveStepData))




def propagate_solve_in_thm
  (thm_data : Array EmbedData) (tag : Nat)
  (ltx : List (Array CExpr)) (ltx_handler : Nat → (Nat × Nat))
  (assign : List (Nat × Nat)) -- (lnode idx, gnode idx) ; should be derived from solve-unification ; lnodes should have tag corresponding to thm_data
  : List (Nat × Nat) × List (Nat × CExpr) × List (Nat × Nat × Nat) :=
  -- fst : (lnode idx, gnode idx) pairs that correspond to assignements, after propagation
  -- snd : (lnode idx, new_goal_type) new goals after propagation
  -- third : (gnode idx, tag, lnode idx) to be added for futher propagation outside of the thm
  let rec propa (lidx gidx : Nat) (sofar_inner : Array (Option Nat)) (sofar_outer : List (Nat × Nat × Nat)) : Option ((Array (Option Nat)) × List (Nat × Nat × Nat)) :=
    let (p,i) := ltx_handler gidx
    let gt := (ltx.get! p).get! i
    let lt := thm_data.get! lidx
    let uni := CExpr.MatchAssignSolutions gt lt.cexpr
    match uni with
    | .none => .none
    | .some L =>
          L.foldl
            (fun inter (gi,t,li) =>
                match inter with
                | .none => .none
                | .some (A, l) =>
                      if t == tag
                      then
                        let nA := Array.assignOrFail li gi A
                        match nA with
                        | .none => .none
                        | .some (NA) => .some (NA,l)
                      else .some (A, (gi,t,li) :: l)
            )
            (.some (sofar_inner, sofar_outer))
  let propagated := assign.foldl
    (fun V (lidx, gidx) =>
      match V with
      | .some (si, so) => propa lidx gidx si so
      | .none => .none
      )
    (Option.some (Array.mkArray thm_data.size (.none : Option Nat),[]))


-- def propagate_solve
--   (unif_outcome : List (Nat × (Nat × Nat))) -- from CExpr.MatchAssignSolutions
--   (backsteps : List (Nat × BackStepData)) :
--   List (Nat × (Nat × Nat)) ×
