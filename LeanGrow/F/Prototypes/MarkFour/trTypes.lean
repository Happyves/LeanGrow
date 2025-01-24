
import LeanGrow.F.Data.CExpr.Types




inductive BackTree where
| fail
| ofAssign (value : CExpr)
| ofUni (uniId : Nat) (value : CExpr)
| ofPropa (uniId goal_id : Nat) (newtype : CExpr) (bdirs : (List Nat)) (gdirs : (List Nat)) (args : List BackTree)
| ofGoal (id : Nat) (type : CExpr) (bdirs : (List Nat)) (gdirs : (List Nat)) (args : List BackTree)
| ofBack (id : Nat) (thm : Lean.Name) (bdirs : Array (List Nat)) (gdirs : Array (List Nat)) (args : Array BackTree) -- add levels
| ofIntro (gid : Nat) (type_head : CExpr) (gnIdxAndTy : List (Nat × CExpr)) (bdirs : (List Nat)) (gdirs : (List Nat)) (args : List BackTree)
deriving Inhabited, BEq, Repr
-- RBNode might be better for dirs entries ? or ordered lists so that we can quit search faster ?

structure BackState where
  id_gen_back : Nat
  id_gen_goal : Nat
  id_gen_assign : Nat
  active_goals : List (Nat × CExpr)
  bt : BackTree
deriving Inhabited, BEq, Repr
