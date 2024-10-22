
import LeanGrow.F.Data.CExpr.Types



structure GoalData where
  goalId : Nat
  backStepOrigin : Nat
  posi : Nat
  type : CExpr
  deps : List (Nat × Nat)


structure BackStepData where
  backStepId : Nat
  exactAsm : Option Nat
  assembly : List (Nat × Lean.Name × Array EmbedData)
  targetIds : List Nat
  instantAssigns : List (Nat × Nat × CExpr) -- tag, position in thm, assignements
  subgoals : List GoalData
