
import LeanGrow.F.Search.BackwardData.tTypes


#check 1

def assemble_cexpr_step
  (solveStatusB : List (Array Bool)) (sSB_handler : Nat → (Nat × Nat)) (sSB_paging : Nat)
  (solveStatusG : List (Array (Option Nat))) (sSG_handler : Nat → (Nat × Nat)) (sSG_paging : Nat)
  (backStep_dict : List (Nat × BackStepData))
  (goal_dict : List (Nat × GoalData))
  (goalId : Nat)
  (assignCache : List (Nat × Nat × CExpr))
  : Option (CExpr × List (Nat × Nat × CExpr)) :=
  let (p,i) := sSG_handler goalId
  match (solveStatusG.get! p).get! i with
  | .none => .none
  | .some b =>
      match backStep_dict.find? (fun x => x.1 == b) with
      | .none => .none
      | .some (_, data) =>
          match data.subgoals with
          | [] => -- a true solution
              match data.exactAsm with
              | .none => .none
              | .some idx => .some (.gnode idx (.ofBvar 42), data.instantAssigns)
          | _ => sorry


/-
Actually, it should be better to separate backsteps and unification steps.
Backsteps whould be assembled by assembly the args of the corresponding thm
and then by applying that thm.
To build the args, we look if they were instant assigned (we should also build
the potential lnodes in these assignements). We should build

-/
