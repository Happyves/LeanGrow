
import LeanGrow.F.Search.BackwardData.tTypes
import LeanGrow.F.Utils.Paging

#check 1

/-
In the current state of things, an actual solution is when we make
a backstep that corresponds to unifying a ltx gnode with a goal,
such that propagation doesn't prevent the solution (clash at previously unified stuff)
and no further goals are generated from propagation

Consider the running example of:
"For example, we could have a first appli of le_trans yielding goals Nat,
1 ≤ .lnode 1 0 and .lnode 1 0 ≤ 4.  We then apply a second le_trans to the second
subgoal, so as to get new goals Nat, 1 ≤ .lnode 1 1 and .lnode 1 1 ≤ .lnode 1 0.
If we have `p : 2 ≤ 3` in the context, and we unify it with .lnode 1 1 ≤ .lnode 1 0, then we should
produce a backstep that has the following data : it solves the initial goal,
produces new subgoals 1 ≤ 2 and 3 ≤ 4, and assigns solutions 2 3 and p."

Here, if we unify a gnode with 1 ≤ 2, then this won't spawn further goals
and we may consider the goal to truely be solved.


A backstep/thm-appli is solved if all its subgoals are.
A goal is solved if one of the backsteps/thm-applis that target it are,
or when a unification as described above occurs.
-/


def BackStepData.isTrueSolution (d : BackStepData) : Bool := d.subgoals.isEmpty


inductive Helper where
| ofB (b : Nat) (g : Nat)
| ofG (id : Nat)
deriving Inhabited, BEq, Repr


partial def propagate_true_solution
  (solveStatusB : List (Array Bool)) (sSB_handler : Nat → (Nat × Nat)) (sSB_paging : Nat)
  (solveStatusG : List (Array (Option Nat))) (sSG_handler : Nat → (Nat × Nat)) (sSG_paging : Nat)
  (backStep_dict : List (Nat × BackStepData))
  (goal_dict : List (Nat × GoalData))
  (backstepId : Nat) :
  (List (Array Bool)) × (List (Array (Option Nat))) :=
  let rec main_back (back : Nat) (sSB : List (Array Bool)) (sSG : List (Array (Option Nat))):
    (List (Nat × Nat)) × (List (Array Bool)) × (List (Array (Option Nat))) :=
    --let (p,i) := sSB_handler back
    match backStep_dict.find? (fun x => x.1 == back) with
    | .none => ([],[],[])
    | .some (_, data) =>
        let proceed? := data.subgoals.foldl
          (fun B g =>
            if B
            then
              let (sp,si) := sSG_handler g.goalId
              let sol? := (solveStatusG.get! sp).get! si
              match sol? with
              | .none => false
              | _ => true
            else false
            )
          true
        if proceed?
        then
          let nsSB := PageingSet sSB sSB_handler sSB_paging false back true
          (data.targetIds.map (fun x => (back,x)), nsSB, sSG)
        else
          ([], sSB, sSG)
  let rec main_goal (back goal : Nat) (sSB : List (Array Bool)) (sSG : List (Array (Option Nat))):
    (Nat) × (List (Array Bool)) × (List (Array (Option Nat))) :=
    --let (p,i) := sSB_handler back
    match goal_dict.find? (fun x => x.1 == back) with
    | .none => (0,[],[])
    | .some (_, data) =>
        let nsSG := PageingSet sSG sSG_handler sSG_paging .none goal (.some back)
        (data.backStepOrigin, sSB, nsSG)
  let rec main (sSB : List (Array Bool)) (sSG : List (Array (Option Nat))) :
    List Helper → (List Helper) × (List (Array Bool)) × (List (Array (Option Nat)))
    | [] => ([], sSB, sSG)
    | .ofB b g :: more =>
          let (next, nsSB, nsSG) := main_goal b g sSB sSG
          main nsSB nsSG ((.ofG next) :: more)
    | .ofG b :: more =>
          let (next, nsSB, nsSG) := main_back b sSB sSG
          main nsSB nsSG ((next.map (fun (x,y) => .ofB x y)) ++ more)
  (main solveStatusB solveStatusG [.ofG backstepId]).2



def update_solve
  (solveStatusB : List (Array Bool)) (sSB_handler : Nat → (Nat × Nat)) (sSB_paging : Nat)
  (solveStatusG : List (Array (Option Nat))) (sSG_handler : Nat → (Nat × Nat)) (sSG_paging : Nat)
  (backStep_dict : List (Nat × BackStepData))
  (goal_dict : List (Nat × GoalData))
  (backstepId : Nat)  (ng : List GoalData) :
  (List (Array Bool)) × (List (Array (Option Nat))) :=
  match ng with
  | [] => -- a true solution
      propagate_true_solution solveStatusB sSB_handler sSB_paging solveStatusG sSG_handler sSG_paging backStep_dict goal_dict backstepId
  | _ =>
      let nsSB := PageingSet solveStatusB sSB_handler sSB_paging false backstepId false
      let nsSG := ng.foldl
          (fun sSG g =>
            PageingSet sSG sSG_handler sSG_paging .none g.goalId .none
            )
          solveStatusG
      (nsSB, nsSG)
