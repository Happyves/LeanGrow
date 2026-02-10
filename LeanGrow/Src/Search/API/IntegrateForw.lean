
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrowBeta.Search.IntroTree.Operations
import LeanGrowBeta.Search.BackTree.Operations
import LeanGrowBeta.Search.Types
import LeanGrowBeta.Core.Embedding.UnifyFEBT
import LeanGrowBeta.Search.API.UnifyCore
import LeanGrowBeta.Search.API.UnifClaches
import LeanGrowBeta.Search.API.DepsCache
import LeanGrowBeta.Search.Score.Regularisation



open Lean Meta



def mergeGoalsForForwIdS (target_gu_id : Nat) (IT : IntroTree (List Nat)):=
  @IntroTree.mergeGoalsForForwId
    (List Nat) _ (List.orderedContains) (List.orderedUnion) []
    target_gu_id IT



def uniFEwBTMainS
  (l1 : LocalContext) (l2 : LocalInstances) (constr : List Nat)
  (revCountMax : Nat) (E : Expr) (T : PaIn (List Nat))
  : MetaM (Prod5 UInt8 (List Nat) (ListProd3 (List Nat) (ListProd3 Nat Nat Expr) (ListProd3 Nat Nat Level)) LocalContext LocalInstances) :=
  PaIn.uniFEwBTMain
    List.isEmpty (List.orderedIntersect) (List.orderedUnion) (List.orderedDiff)
    [] l1 l2 constr revCountMax E T

#check 1


def insertForwAtForwIdsS (l1 : LocalContext) (l2 : LocalInstances) (termUGnodes : List Nat)
  (IT : IntroTree (List Nat)) (new_forw_id : Nat) (new_forw : Expr)
  : MetaM (Prod3 (IntroTree (List Nat)) LocalContext LocalInstances) :=
  @IntroTree.insertForwAtForwIds (List Nat) _
    (List.orderedContains) id (List.orderedUnion)
    (fun x => [x]) [] (List.orderedInsertOrLeave) l1 l2 termUGnodes IT
    new_forw_id new_forw


/--
Continuation takes ugId of new addition and the state
-/
def integrateForwardStd (l1 : LocalContext) (l2 : LocalInstances) (revCountMax : Nat)
  (fmd : ForwMetaData) (term : Expr) (termUGnodes : List Nat)
  (st : SearchState (List Nat))
  : MetaM (Prod5 Nat Expr (SearchState (List Nat)) LocalContext LocalInstances) :=
  do --trace set Tracing.Flags.none in do
  withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
  let termUGnodes := termUGnodes.mergeSort -- paranoia ?
  -- adding decl
  let type ← whnfAtMostI <| ← inferType term
  let g? ← isProp type
  let name := if g? then gnode st.id_gen_forw else unode st.id_gen_forw
  let .mk _ l1 l2 ← WithLetDecl name type term l1 l2
  mtrace on .zero with s!"[integrateForwardStd] added {name} of type {← ppExpr type} and term {← ppExpr term}"
  let st := if g? then st else {st with uNodes := st.uNodes.push st.id_gen_forw}
  let st := {st with id_gen_forw := st.id_gen_forw + 1}
  let decl ← (⟨name⟩ : FVarId).GetDecl l1 l2
  -- undate deps
  let st := updateDepsCachesPreCompNoMonad decl termUGnodes st
  mtrace on .one with s!"[integrateForwardStd] depsCache {repr <| st.depsCache.mapFinIdx (fun i j _ => (i,j.map LocalDecl.fvarId))}"
  -- update height and depths
  let st := {st with forwHeights := updateForwHeight st.forwHeights termUGnodes}
  let st := {st with forwDepths := updateForwDepth st.forwDepths termUGnodes}
  mtrace on .one with s!"[integrateForwardStd] new forwHeights {st.forwHeights}"
  mtrace on .one with s!"[integrateForwardStd] new forwDepths {st.forwDepths.map (fun x => x.depth)}"
  -- update metadata
  let st := {st with forwMetadata := st.forwMetadata.push fmd}
  mtrace on .one with s!"[integrateForwardStd] new forwMetadata {repr st.forwMetadata}"
  -- insert in introtree
  let .mk IT l1 l2 ← insertForwAtForwIdsS l1 l2
    termUGnodes st.introTree (st.id_gen_forw - 1) type
  let st : SearchState (List Nat) := {st with introTree := IT}
  mtrace on .zero with s!"[integrateForwardStd] introTree {st.introTree.pp 0}"
  -- unify
  let goalPaIn := mergeGoalsForForwIdS (st.id_gen_forw - 1) st.introTree
  mtrace on .zero with s!"[integrateForwardStd] goalPaIn {← goalPaIn.ppS l1 l2 [] 0}"
  let .mk yes? _ unifs l1 l2 ← uniFEwBTMainS l1 l2
    goalPaIn.getIndicesS revCountMax type goalPaIn
  if yes? != 3
  then
    mtrace on .zero with s!"[integrateForwardStd] uniFEwBTMainS fail "
    return .mk (st.id_gen_forw - 1) type st l1 l2
  else
    mtrace on .zero with s!"[integrateForwardStd] uniFEwBTMainS success: {← unifs.foldlM [] (fun is ta la R => return (is, ← ta.foldlM [] (fun x y z w => return (x,y, ← ppExpr z) :: w)) :: R)}"
    let .mk st l1 l2 : Prod3  (SearchState (List Nat)) LocalContext LocalInstances := ← unifs.foldlM (.mk st l1 l2) (fun goalInds ta la (.mk st l1 l2) => do
      let .mk ta l1 l2 ← ta.foldlM ((.mk ListProd3.nil l1 l2) : Prod3 (ListProd3 Nat Nat Expr) _ _) (fun x y z (.mk R l1 l2) => do
        let .mk z l1 l2 ← mvarifyTnodesRecWiContextIn z l1 l2
        return .mk (.cons x y z R) l1 l2)
      let .mk la l1 l2 ← la.foldlM ((.mk ListProd3.nil l1 l2) : Prod3 (ListProd3 Nat Nat Level) _ _) (fun x y z (.mk R l1 l2) => do
        let .mk z l1 l2 ← mvarifyLTnodesIn z l1 l2
        return .mk (.cons x y z R) l1 l2)
      let st ← goalInds.foldlM (fun st goalId => do
        match st.goalSpawn[goalId]! with
        | .some b p =>
            let ta := ListProd3.cons b p (.fvar ⟨name⟩) ta
            let st ← computeNewClashesMain l1 l2 st ta la -- bumps id_gen_uni
            let st := {st with backTree := st.backTree.addUnis st.id_gen_apass [st.id_gen_uni - 1] ta}
            return st
        | .none =>
            let st ← computeNewClashesMain l1 l2 st ta la -- bumps id_gen_uni
            let st := {st with backTree := st.backTree.addUnis st.id_gen_apass [st.id_gen_uni - 1] ta}
            return st
        ) st
      return .mk st l1 l2
      )
    mtrace on .zero with s!"[integrateForwardStd] backTree : {← st.backTree.pp 0}"
    return .mk (st.id_gen_forw - 1) type st l1 l2


#check mvarifyTnodesRecWiContextIn
#check mvarifyLTnodesIn

-- #exit

#check IntroTree.hasForw?
#check IntroTree.hasForwEAtForwIds?

def hasForwAtGoalIdS (l1 : LocalContext) (l2 : LocalInstances)
  (target_goal_id : Nat) (revCountMax : Nat) (ce : Expr) (T : IntroTree (List Nat)) :=
  @IntroTree.hasForwAtGoalId? (List Nat) _ target_goal_id
    (List.orderedContains) List.isEmpty id
    (List.orderedIntersect) (List.orderedUnion) []
    revCountMax l1 l2 ce T

def forwardDuplicateG? (l1 : LocalContext) (l2 : LocalInstances) (target_goal_id : Nat) (revCountMax : Nat) (ce : Expr) (T : IntroTree (List Nat))
  : MetaM (Prod3 Bool LocalContext LocalInstances) := do
  if ← IsProp ce l1 l2 then hasForwAtGoalIdS l1 l2 target_goal_id revCountMax ce T else return .mk false l1 l2


def hasForwEAtForwIdsS (l1 : LocalContext) (l2 : LocalInstances)
  (revCountMax : Nat) (target_forw_ids : List Nat) (ce : Expr) (IT : IntroTree (List Nat)) :=
  @IntroTree.hasForwEAtForwIds? (List Nat) _ List.isEmpty id id
    (List.orderedIntersect) (List.orderedUnion) []
    revCountMax l1 l2 target_forw_ids ce IT

def forwardDuplicateF? (l1 : LocalContext) (l2 : LocalInstances)
  (target_forw_ids : List Nat) (revCountMax : Nat) (ce : Expr) (T : IntroTree (List Nat))
  : MetaM (Prod3 Bool LocalContext LocalInstances) := do
  if ← IsProp ce l1 l2 then hasForwEAtForwIdsS l1 l2 revCountMax target_forw_ids ce T else return .mk false l1 l2
