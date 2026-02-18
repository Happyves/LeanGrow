
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Search.IntroTree.Operations
import LeanGrow.Src.Search.BackTree.Operations
import LeanGrow.Src.Search.Types
import LeanGrow.Src.Core.Embedding.UnifyFEBT
import LeanGrow.Src.Search.API.UnifyCore
import LeanGrow.Src.Search.API.UnifClaches
import LeanGrow.Src.Search.API.DepsCache
import LeanGrow.Src.Search.Score.Regularisation



open Lean Meta


def mergeGoalsForForwIdS (target_gu_id : Nat) (IT : IntroTree UInt32Array):=
  @IntroTree.mergeGoalsForForwId
    UInt32Array _ _ (fun x y => y.oContains x.toUInt32) UInt32Array.union UInt32Array.empty
    target_gu_id IT



def uniFEwBTMainS
  (l1 : LocalContext) (l2 : LocalInstances) (constr : UInt32Array)
  (revCountMax : Nat) (E : Expr) (T : PaInG UInt32Array)
  : MetaM (Prod5 UInt8 UInt32Array (ListProd3 UInt32Array (ListProd3 Nat Nat Expr) (ListProd3 Nat Nat Level)) LocalContext LocalInstances) :=
  PaInG.uniFEwBTMain
    UInt32Array.isEmpty UInt32Array.inter UInt32Array.union UInt32Array.diff
    UInt32Array.empty l1 l2 constr revCountMax E T

#check 1


def insertForwAtForwIdsS (l1 : LocalContext) (termUGnodes : UInt32Array)
  (IT : IntroTree UInt32Array) (new_forw_id : Nat) (new_forw_type : Expr) (new_forw_fv : FVarId)
  : MetaM (Prod (IntroTree UInt32Array) LocalContext) :=
  @IntroTree.insertForwAtForwIds UInt32Array _
    (fun x y => y.oContains x.toUInt32) UInt32Array.diff (fun x => UInt32Array.single x.toUInt32)
    UInt32Array.empty (fun x y => y.oInsert x.toUInt32) UInt32Array.isEmpty
    (fun x => x[0]!.toNat)
    l1 termUGnodes IT new_forw_id new_forw_type new_forw_fv

#check 1



/--
Continuation takes ugId of new addition and the state
-/
def integrateForwardStd (l1 : LocalContext) (l2 : LocalInstances) (revCountMax : Nat)
  (fmd : ForwMetaData) (term : Expr) (termUGnodes : UInt32Array)
  (st : SearchState UInt32Array)
  : MetaM (Prod6 Nat FVarId Expr (SearchState UInt32Array) LocalContext LocalInstances) :=
  do
  mtracing
  -- adding decl
  let type ← withLCtx l1 l2 <| whnfAtMostI <| ← inferType term
  let g? ← IsProp type l1 l2
  let name := if g? then gnode st.id_gen_forw else unode st.id_gen_forw
  let .mk _ l1 l2 ← WithLetDecl name type term l1 l2
  mtrace on .zero with s!"[integrateForwardStd] added {name} of type {← ppExpr type} and term {← ppExpr term}"
  let st := if g? then st else {st with uNodes := st.uNodes.push st.id_gen_forw}
  let st : SearchState UInt32Array := {st with id_gen_forw := st.id_gen_forw + 1}
  -- update deps
  let st ← updateDepsCachesPreCompNoMonad l1 l2 (.mk name) st
  mtrace on .one with s!"[integrateForwardStd] depsCache (forward transitive) {repr <| st.depsCache.mapIdx (fun i j => (i,j.fTrans))}"
  -- update height and depths
  let st := {st with forwHeights := updateForwHeight st.forwHeights termUGnodes}
  let st := {st with forwDepths := updateForwDepth st.forwDepths termUGnodes}
  mtrace on .one with s!"[integrateForwardStd] new forwHeights {st.forwHeights}"
  mtrace on .one with s!"[integrateForwardStd] new forwDepths {st.forwDepths.map (fun x => x.depth)}"
  -- update metadata
  let st := {st with forwMetadata := st.forwMetadata.push fmd}
  mtrace on .one with s!"[integrateForwardStd] new forwMetadata {repr st.forwMetadata}"
  -- insert in introtree
  let .mk IT l1 ← insertForwAtForwIdsS l1
    termUGnodes st.introTree (st.id_gen_forw - 1) type (.mk name)
  let st : SearchState UInt32Array := {st with introTree := IT}
  mtrace on .zero with s!"[integrateForwardStd] introTree {st.introTree.pp 0}"
  -- unify
  let goalPaIn := mergeGoalsForForwIdS (st.id_gen_forw - 1) st.introTree
  mtrace on .zero with s!"[integrateForwardStd] goalPaIn {← goalPaIn.ppS l1 l2 [] 0}"
  let .mk yes? _ unifs l1 l2 ← uniFEwBTMainS l1 l2
    goalPaIn.getIndicesS revCountMax type goalPaIn
  if yes? != 3
  then
    mtrace on .zero with s!"[integrateForwardStd] uniFEwBTMainS fail "
    return .mk (st.id_gen_forw - 1) (.mk name) type st l1 l2
  else
    mtrace on .zero with s!"[integrateForwardStd] uniFEwBTMainS success: {← unifs.foldlM [] (fun is ta la R => return (is, ← ta.foldlM [] (fun x y z w => return (x,y, ← ppExpr z) :: w)) :: R)}"
    let .mk st l1 l2 : Prod3  (SearchState UInt32Array) LocalContext LocalInstances := ← unifs.foldlM (.mk st l1 l2) (fun goalInds ta la (.mk st l1 l2) => do
      let .mk ta l1 l2 ← ta.foldlM ((.mk ListProd3.nil l1 l2) : Prod3 (ListProd3 Nat Nat Expr) _ _) (fun x y z (.mk R l1 l2) => do
        let .mk z l1 l2 ← mvarifyTnodesRec z l1 l2
        return .mk (.cons x y z R) l1 l2)
      let .mk la l1 l2 ← la.foldlM ((.mk ListProd3.nil l1 l2) : Prod3 (ListProd3 Nat Nat Level) _ _) (fun x y z (.mk R l1 l2) => do
        let .mk z l1 l2 ← mvarifyLTnodesIn z l1 l2
        return .mk (.cons x y z R) l1 l2)
      let st ← goalInds.foldlM st (fun goalId st => do
        let goalId := goalId.toNat
        match st.goalSpawn[goalId]! with
        | .some b p =>
            let ta := ListProd3.cons b p (.fvar ⟨name⟩) ta
            let st ← computeNewClashesMain l1 l2 st ta la -- bumps id_gen_uni
            let st := {st with backTree := st.backTree.addUnis st.id_gen_apass (.single (st.id_gen_uni - 1).toUInt32) ta}
            return st
        | .none =>
            let st ← computeNewClashesMain l1 l2 st ta la -- bumps id_gen_uni
            let st := {st with backTree := st.backTree.addUnis st.id_gen_apass (.single (st.id_gen_uni - 1).toUInt32) ta}
            return st
        )
      return .mk st l1 l2
      )
    mtrace on .zero with s!"[integrateForwardStd] backTree : {← st.backTree.pp 0}"
    return .mk (st.id_gen_forw - 1) (.mk name) type st l1 l2


#check mvarifyLTnodesIn

#check IntroTree.hasForwEAtForwIds?
#check Expr.getGUFVarsIds



def hasForwAtGoalIdS (l1 : LocalContext)
  (target_goal_id : Nat) (revCountMax : Nat) (ce : Expr) (T : IntroTree UInt32Array) :=
  @IntroTree.hasForwAtGoalId? UInt32Array _ _ target_goal_id
    (fun x y => y.oContains x.toUInt32) UInt32Array.isEmpty
    UInt32Array.inter UInt32Array.union UInt32Array.empty
    revCountMax l1 ce T

def forwardDuplicateG? (l1 : LocalContext) (target_goal_id : Nat) (revCountMax : Nat) (ce : Expr) (T : IntroTree UInt32Array)
  : MetaM (Prod Bool LocalContext) := do
  let gufv := ce.getGUFVarsIds
  let guInds := gufv.foldl (fun R i =>
    match i.name with
    | .num _ i => R.oInsert i.toUInt32
    | _ => panic! s!"[forwardDuplicateG?] bad fvar {i.name}"
    ) UInt32Array.empty
  @IntroTree.forwardDuplicateG?' _ _ _ target_goal_id
    (fun x y => y.oContains x.toUInt32) UInt32Array.isEmpty
    UInt32Array.inter UInt32Array.union UInt32Array.empty
    revCountMax l1 ce guInds T


def hasForwEAtForwIdsS (l1 : LocalContext)
  (revCountMax : Nat) (target_forw_ids : UInt32Array) (ce : Expr) (IT : IntroTree UInt32Array) :=
  @IntroTree.hasForwEAtForwIds? UInt32Array _ UInt32Array.isEmpty
    UInt32Array.inter UInt32Array.union UInt32Array.diff UInt32Array.empty
    revCountMax l1 target_forw_ids ce IT

def forwardDuplicateF? (l1 : LocalContext)
  (target_forw_ids : UInt32Array) (revCountMax : Nat) (ce : Expr) (T : IntroTree UInt32Array)
  : MetaM (Prod Bool LocalContext) := do
  let gufv := ce.getGUFVarsIds
  let guInds := gufv.foldl (fun R i =>
    match i.name with
    | .num _ i => R.oInsert i.toUInt32
    | _ => panic! s!"[forwardDuplicateG?] bad fvar {i.name}"
    ) UInt32Array.empty
  @IntroTree.forwardDuplicateF?' _ _ UInt32Array.isEmpty
    UInt32Array.inter UInt32Array.union UInt32Array.diff UInt32Array.empty
    revCountMax l1 target_forw_ids ce guInds T
