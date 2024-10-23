
import LeanGrow.F.Data.CExpr.Types


inductive GoalType where
| ofBack (_ : Nat)
| ofUni (_ : Nat)
deriving Inhabited, BEq, Repr

structure GoalData where
  goalId : Nat
  backStepOrigin : GoalType
  type : CExpr
  deps : List (Nat × Nat)


structure BackStepData where
  backStepId : Nat
  ofThm : Lean.Name
  embData : Array EmbedData
  targetId : Nat
  instantAssigns : List (Nat × CExpr) -- position in thm, assignements
  subgoals : List (Nat × GoalData) -- position in thm, goal


structure UniData where
  uniStepId : Nat
  targetId : Nat
  solveGnodeId : Nat
  assigns : List (Nat × Nat × CExpr) -- tag, pos, val
  subgoalSubst : List (GoalType × GoalData) -- original id, updated goal
