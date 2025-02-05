
import LeanGrow.F.Data.CExpr.Types
import LeanGrow.F.Data.Unification.EmbedGoalWInferWUnis


open Lean

inductive BackType
| ofThm (_ : Name) | ofLocal (gnodeIdx : Nat)
deriving Inhabited, BEq, Repr


inductive BackTree where
| fail
| ofAssign (value : CExpr)
| ofUni (uniId : Nat) (value : CExpr)
| ofPropa (uniId goal_id : Nat) (newtype : CExpr) (bdirs : (List Nat)) (gdirs : (List Nat)) (args : List BackTree)
| ofGoal (id : Nat) (type : CExpr) (bdirs : (List Nat)) (gdirs : (List Nat)) (args : List BackTree)
| ofBack (id : Nat) (thm : BackType) (bdirs : Array (List Nat)) (gdirs : Array (List Nat)) (args : Array BackTree) -- add levels
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


inductive IntroTree where
| leaf (gids : List Nat) (ltx : List (Nat × CExpr))
| node (gids : List Nat) (ltx : List (Nat × CExpr)) (kidsWdirs : List (List Nat × IntroTree))
deriving Inhabited, Repr, BEq



structure SearchState where
  back : BackState
  forw : IntroTree
  forw2 : List (Array CExpr)
  ltx_handler : Nat → (Nat × Nat)
  forwID : Nat
  fctx : FixCtx -- it would be better to seperate the gnode info and lnode info
                -- so that we can do forward and backward steps independently of backsteps
  ltx_assemmbly : List (Nat × BackType × Array CExpr) -- add universe levels
  unif_assign : List (Nat × (List (Nat × Nat × CExpr) × List (Name × Level))) -- (uni_id, params assignements)
  back_memo : List (Nat × List BackType)
  uni_memo : List (Nat × Nat)
  uni_claches : List (Nat × Nat)
deriving Inhabited--, Repr, BEq


structure TriggerState where
  forwID : Nat
  id_gen_back : Nat
  id_gen_goal : Nat
  id_gen_uni : Nat
  new_gnodes : List (Nat × List (Nat × CExpr))
  new_goals : List (Nat × CExpr)
  branches_to_add : List BackTree
deriving Inhabited, Repr, BEq
