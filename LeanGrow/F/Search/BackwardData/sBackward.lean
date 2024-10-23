

import LeanGrow.F.Data.Unification.UnifyForBack
import LeanGrow.F.Search.BackwardData.sTypes
import LeanGrow.F.Utils.Array
import Mathlib.Data.List.Sort

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

open Lean

def integrate_backward_outcome (goalIdCounter backStepIdCounter : Nat)
  (thm_name : Name) (embData : Array EmbedData) (taget_id : Nat)
  (assigned nextGoals: List (Nat × CExpr)) :
  BackStepData × List GoalData × Nat :=
  let gd : (List (Nat × GoalData)) × Nat :=
    nextGoals.foldl
      (fun (L,c) (n,ce) =>
          ((n,⟨c, .ofBack backStepIdCounter, ce, compute_subgoal_deps ce⟩) :: L,c+1)
      )
      ([], goalIdCounter)
  (⟨backStepIdCounter, thm_name, embData, taget_id, assigned, gd.1⟩, gd.1.map Prod.snd ,gd.2)




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



def List.eraseF (p : α → Bool) : List α → List α
| [] => []
| x :: l => if p x then l else x :: (List.eraseF p l)





def propagate_uni_assign_step
  (tag lidx : Nat) (guni : SolNodeExpr)
  (ltx : List (Array CExpr)) (ltx_handler : Nat → (Nat × Nat))
  (backStep_dict : List (Nat × BackStepData))
  (sofar : List (Nat × Array (Option SolNodeExpr)))
  : Option (List (Nat × Array (Option SolNodeExpr)) × List (Nat × Nat × SolNodeExpr)) :=
    match sofar.find? (fun x => x.1 == tag) with
    | .none =>
        match backStep_dict.find? (fun x => x.1 == tag) with
        | .none => .none
        | .some (_, backData) =>
            match backData.instantAssigns.find? (fun x => x.1 == lidx) with
            | .some (_, already) =>
                match already, guni with
                | .gnode i _, .ofGNode j => if i == j then .some (sofar, []) else .none
                | ce, .ofCExpr ec => if ce == ec then .some (sofar, []) else .none
                | _, _ => .none
            | .none =>
                  match guni with
                  | .ofGNode gidx =>
                        let (gp,gi) := ltx_handler gidx
                        let gt := (ltx.get! gp).get! gi
                        let uni := CExpr.MatchAssignSolutions gt (backData.embData.get! lidx).cexpr
                        match uni with
                        | .none => .none
                        | .some res =>
                              let Anew := Array.mkArray backData.embData.size (.none)
                              let A := Anew.set! lidx (.some (.ofGNode gidx))
                              .some ((tag, A) :: sofar, res)
                  | .ofCExpr ce =>
                        let uni := CExpr.MatchAssignSolutions ce (backData.embData.get! lidx).cexpr
                        match uni with
                        | .none => .none
                        | .some res =>
                              let Anew := Array.mkArray backData.embData.size (.none)
                              let A := Anew.set! lidx (.some (.ofCExpr ce))
                              .some ((tag, A) :: sofar, res)
    | .some (_, embSofar) =>
        match embSofar.get! lidx with
        | .some j => if j == guni then .some (sofar,[]) else .none
        | .none =>
            match backStep_dict.find? (fun x => x.1 == tag) with
            | .none => .none
            | .some (_, backData) =>
                match backData.instantAssigns.find? (fun x => x.1 == lidx) with
                | .some (_, already) =>
                    match already, guni with
                    | .gnode i _, .ofGNode j => if i == j then .some (sofar, []) else .none
                    | ce, .ofCExpr ec => if ce == ec then .some (sofar, []) else .none
                    | _, _ => .none
                | .none =>
                      match guni with
                      | .ofGNode gidx =>
                          let (gp,gi) := ltx_handler gidx
                          let gt := (ltx.get! gp).get! gi
                          let uni := CExpr.MatchAssignSolutions gt (backData.embData.get! lidx).cexpr
                          match uni with
                          | .none => .none
                          | .some res =>
                                let interim := sofar.eraseF (fun x => x.1 == tag)
                                .some ((tag, embSofar.set! lidx (.some (.ofGNode gidx))) :: interim, res)
                      | .ofCExpr ce =>
                            let uni := CExpr.MatchAssignSolutions ce (backData.embData.get! lidx).cexpr
                            match uni with
                            | .none => .none
                            | .some res =>
                                let interim := sofar.eraseF (fun x => x.1 == tag)
                                .some ((tag, embSofar.set! lidx (.some (.ofCExpr ce))) :: interim, res)



partial def propagate_uni_assign
  (init : List (ℕ × ℕ × SolNodeExpr))
  (ltx : List (Array CExpr)) (ltx_handler : Nat → (Nat × Nat))
  (backStep_dict : List (Nat × BackStepData)) :
  Option (List (Nat × Array (Option SolNodeExpr))) := -- tag, assignments in form of array where idx is lnode idx and enty is assignement
    let rec go (sofar : List (Nat × Array (Option SolNodeExpr)))  : List (Nat × Nat × SolNodeExpr) → Option (List (Nat × Array (Option SolNodeExpr)))
      | [] => .some sofar
      | (t,l,pg) :: todo =>
          match propagate_uni_assign_step t l pg ltx ltx_handler backStep_dict sofar with
          | .none => .none
          | .some (next,toPropa) =>
                let nextPropa := toPropa ++ todo
                go next nextPropa
    go [] init




/-
TODO next: same idea as `propagate_lnode` to get new subgoals,
but note that this should also be over all of the `List (Nat × Array (Option SolNodeExpr))`
in parallel, since assigned lnodes with one tag may also be among the unsolved goals
of other taged thm-applis.

Note:
After propagation, there may be new subgoals corresponding to old ones, but with
more gnodes or constant expressions. It may be the case that for the old goals, there
were backsteps implying them. We could then propagate this to the new subgoals, since
the thm application remains valid after substituing lnodes with gnodes or constant expressions
-/


partial def propagate_uni_newgoals
  (uniSolveId : Nat) (goalIdCounter : Nat)
  (assignments : List (Nat × Array (Option SolNodeExpr)))
  (backStep_dict : List (Nat × BackStepData)) :
  List (GoalType × GoalData) × List (Nat × Nat × CExpr) × Nat :=
  let oa := List.mergeSort (fun x y => x.1 ≤ y.1) assignments
  -- make use of the fact that backsteps can only inherit lnodes from previous backsteps, with smaller Id
  let rec process_1 (ctx : List (Nat × Array (Option SolNodeExpr))) : CExpr → CExpr
    | .lnode i o (.some t) =>
          match ctx.find? (fun x => x.1 == t) with
          | .none => .lnode i o (.some t)
          | .some (_,ce) =>
                match ce.get! i with
                | .none => .lnode i o (.some t)
                | .some (.ofGNode j) => .gnode j (.ofBvar 42)
                | .some (.ofCExpr nce) => nce
    | .app f a => .app (process_1 ctx f) (process_1 ctx a)
    | .lam n f a i => .lam n (process_1 ctx f) (process_1 ctx a) i
    | .forallE n f a i => .forallE n (process_1 ctx f) (process_1 ctx a) i
    | .letE n f a z i => .letE n (process_1 ctx f) (process_1 ctx a) (process_1 ctx z) i
    | .proj n i a => .proj n i (process_1 ctx a)
    | ce => ce
  let rec process_2 (goalIdCounter : Nat) (tag : Nat) (A : Array (Option SolNodeExpr)) (ctx : List (Nat × Array (Option SolNodeExpr))) : List (GoalType × GoalData) × List (Nat × Nat × CExpr) × Nat :=
    match backStep_dict.find? (fun x => x.1 == tag) with
    | .none => ([], [], goalIdCounter)
    | .some (_, data) =>
          let tofix := data.subgoals
          tofix.foldl
            (fun (GL,AL,k) (posi, ⟨_,_,typ,_⟩) =>
              match A.get! posi with
              | .some res =>
                  let eres : CExpr :=
                    match res with
                    | (.ofGNode j) => .gnode j (.ofBvar 42)
                    | (.ofCExpr nce) => nce
                  (GL, (tag, posi, eres) :: AL, k+1)
              | .none =>
                  let nt := process_1 ((tag, A) :: ctx) typ
                  let ndep := compute_subgoal_deps nt
                  ((.ofBack tag, ⟨k,.ofUni uniSolveId ,nt,ndep⟩) :: GL, AL, k+1)
                  -- in particular, goals in which types aren't updated (because thay have no assign lnodes)
                  -- will be duplicated, but with a different backstepId !
              )
            ([], [], goalIdCounter)
  let rec process_3 (count : Nat) (cacheG : List (GoalType × GoalData)) (cacheA : List (Nat × Nat × CExpr)) (ctx : List (Nat × Array (Option SolNodeExpr))) : List (Nat × Array (Option SolNodeExpr)) → List (GoalType × GoalData) × List (Nat × Nat × CExpr) × Nat
    | [] => (cacheG, cacheA, count)
    | (tag, A) :: rest =>
        let (ng,na,nc) := process_2 count tag A ctx
        process_3 nc (ng ++ cacheG) (na ++ cacheA) ((tag, A) :: ctx) rest
  process_3 goalIdCounter [] [] [] oa




#check List.mergeSort




def integrate_uni_outcome (goalIdCounter uniStepIdCounter : Nat)
  (goalId gidx : Nat)
  (ltx : List (Array CExpr)) (ltx_handler : Nat → (Nat × Nat))
  (backStep_dict : List (Nat × BackStepData)) (goal_dict : List (Nat × GoalData)) :
  Option (UniData × List GoalData × Nat) :=
  let (p,i) := ltx_handler gidx
  let gt := (ltx.get! p).get! i
  match goal_dict.find? (fun x => x.1 == goalId) with
  | .none => .none
  | .some (_, gdata) =>
      match CExpr.MatchAssignSolutions gt gdata.type with
      | .none => .none
      | .some emb =>
          let propa? := propagate_uni_assign emb ltx ltx_handler backStep_dict
          match propa? with
          | .none => .none
          | .some L =>
                if L.isEmpty
                then
                  let main : UniData := ⟨uniStepIdCounter, goalId, gidx, [], []⟩
                  .some (main, [], goalIdCounter+1)
                else
                  let (newGoals, newAssignments, newGoalCounter) := propagate_uni_newgoals uniStepIdCounter goalIdCounter L backStep_dict
                  let main : UniData := ⟨uniStepIdCounter, goalId, gidx, newAssignments, newGoals⟩
                  .some (main, newGoals.map Prod.snd, newGoalCounter)
