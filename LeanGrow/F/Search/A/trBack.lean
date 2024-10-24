
import LeanGrow.F.Search.A.trTypes


open Lean

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


partial def BackTree.modifyAtGoalId (id : Nat) (mod : BackTree → BackTree) : BackTree → BackTree
  | .fail => .fail
  | .ofAssign ce => .ofAssign ce
  | .ofGoal j t => if j == id then mod (.ofGoal j t) else .ofGoal j t
  | .ofBack i n dirs ts =>
      match dirs.findIdx? (fun l => l.contains id) with
      | .none => .ofBack i n dirs ts
      | .some j => .ofBack i n dirs (ts.set! j (BackTree.modifyAtGoalId id mod (ts.get! j)))


def List.replaceByListAt (toAdd : List α) : List α → Nat → List α
  | [], _ => [] -- shouldn't happen
  | _ :: more, 0 => toAdd ++ more
  | h :: more, n+1 => h :: (List.replaceByListAt toAdd more n)

def List.replaceByListWhen (toAdd : List α) (p : α → Bool) : List α → List α
  | [] => []
  | h :: more => if p h then toAdd ++ more else h :: (List.replaceByListWhen toAdd p more)



partial def BackTree.modifyAtGoalId_wUpdates (id : Nat) (rep : List Nat) (mod : BackTree → BackTree) : BackTree → BackTree
  | .fail => .fail
  | .ofAssign ce => .ofAssign ce
  | .ofGoal j t => if j == id then mod (.ofGoal j t) else .ofGoal j t
  | .ofBack i n dirs ts =>
      match dirs.findIdx? (fun l => l.contains id) with
      | .none => .ofBack i n dirs ts
      | .some j => .ofBack i n (dirs.set! j (List.replaceByListWhen rep (fun x => x == id) (dirs.get! j))) (ts.set! j (BackTree.modifyAtGoalId id mod (ts.get! j)))




structure IntegBack where
  new_goals : List (Nat × CExpr)
  tree : BackTree


def integrate_backstep
  (thm_name : Name) (thm_data_size : Nat) (target_goal_id : Nat)
  (assigned newgoals : List (Nat × CExpr))
  (id_gen_back : Nat) (id_gen_goal : Nat)
  (backTree : BackTree) : IntegBack :=
    let common := (newgoals.foldl (fun (l,i) (pos,type) => (((pos,i,type) :: l),i+1)) ([], id_gen_goal)).1
    let new_dirs := common.map (fun x => x.2.1)
    let dirs_new := common.foldl
      (fun A (pos,gId,_) => A.set! pos [gId])
      (Array.mkArray thm_data_size [])
    let new_leaves_1 := (Array.mkArray thm_data_size .fail)
    let new_leaves_2 := assigned.foldl
      (fun A (pos, val) => A.set! pos (.ofAssign val))
      new_leaves_1
    let new_leaves_3 := common.foldl
      (fun A (pos, gId, type) => A.set! pos (.ofGoal gId type))
      new_leaves_2
    let new_branches : BackTree → BackTree := fun _ =>
      .ofBack id_gen_back thm_name dirs_new new_leaves_3
    let finalT := BackTree.modifyAtGoalId_wUpdates target_goal_id new_dirs new_branches backTree
    ⟨common.map Prod.snd, finalT⟩

/-
Next up, unification step:
- change goal-leaf into assign-leaf
- do so for all propagated assignements
- replace goals


-/
