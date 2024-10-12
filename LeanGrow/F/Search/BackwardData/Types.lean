
import LeanGrow.F.Data.CExpr.Types

#check 1



structure GoalData where
  goalId : Nat
  backStepOrigin : Nat
  posi : Nat
  type : CExpr

structure BackStepData where
  backStepId : Nat
  instantAssigns : List (Nat × CExpr)
  subgoals : List Nat -- or List (Nat × CExpr) ? or NodeExpr instean of CExpr, probably ?
  -- also ↑ should have goal ids as well as their position as hyps in the thm application !!
