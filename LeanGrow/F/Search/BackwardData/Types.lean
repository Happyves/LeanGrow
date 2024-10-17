
import LeanGrow.F.Data.CExpr.Types



structure GoalData where
  goalId : Nat
  backStepOrigin : Nat
  posi : Nat
  type : CExpr
  deps : List (Nat × Nat)


-- inductive BackType where
-- | ofBack (thm : Lean.Name) -- or other data, to be used for assembly ?
-- | ofSolve (tags_thms : List (Nat × Lean.Name)) --relating tags and thms

-- inductive AssignType where
-- | ofBack (_ : List (Nat × CExpr)) -- posi, val
-- | ofSolve (_ : List (Nat × Nat × CExpr)) -- tag, posi, val


-- maybe split into back and solve, and make inductive that is union of both ; use same index counter for ids

structure BackStepData where
  backStepId : Nat
  assembly_name : Lean.Name
  assembly_embed : Array EmbedData
  targetId : Nat -- the id of the goal solved by applying this thm
  instantAssigns : List (Nat × CExpr)
  subgoals : List Nat -- or List (Nat × CExpr) ? or NodeExpr instean of CExpr, probably ?
  -- also ↑ should have goal ids as well as their position as hyps in the thm application !!
