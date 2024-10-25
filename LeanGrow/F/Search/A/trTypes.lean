
import LeanGrow.F.Data.CExpr.Types




inductive BackTree where
| fail
| ofAssign (value : CExpr)
| ofGoal (id : Nat) (type : CExpr)
| ofBack (id : Nat) (thm : Lean.Name) (bdirs : Array (List Nat)) (gdirs : Array (List Nat)) (args : Array BackTree)
deriving Inhabited, BEq, Repr         -- RBNode might be better for dirs entries ? or ordered lists so that we can quit search faster ?

structure BackState where
  id_gen_back : Nat
  id_gen_goal : Nat
  active_goals : List (Nat × CExpr)
  bt : BackTree
deriving Inhabited, BEq, Repr


inductive BackStateTree where
| leaf (id : Nat) (s : BackState)
| node (id : Nat) (s : BackState) (dirs : List (List Nat)) (chi : List BackStateTree)
deriving Inhabited, BEq, Repr
