

/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Search.IntroTree.Operations
import LeanGrow.Src.Search.BackTree.Operations
import LeanGrow.Src.Search.Types
import LeanGrow.Src.Search.API.UnifyCore
import LeanGrow.Src.Search.API.UnifClaches
import LeanGrow.Src.Search.API.Intro
import LeanGrow.Src.Search.Score.Regularisation
import LeanGrow.Src.Core.Embedding.UnifyBEFT


open Lean Meta


#check PaInG.uniBEwFTMain
#check IntroTree.mergeLtxForGoalId
#check IntroTree.insertGoalsAtGoalId



def uniBEwFTMainS
  (l1 : LocalContext) (l2 : LocalInstances) (constr : UInt32Array)
  (revCountMax : Nat) (E : Expr) (T : PaInG UInt32Array)
  : MetaM (Prod5 UInt8 UInt32Array (ListProd3 UInt32Array (ListProd3 Nat Nat Expr) (ListProd3 Nat Nat Level)) LocalContext LocalInstances) :=
  PaInG.uniBEwFTMain
    UInt32Array.isEmpty UInt32Array.inter UInt32Array.union UInt32Array.diff
    UInt32Array.empty l1 l2 constr revCountMax E T


#check 1


def mergeLtxForGoalIdS (target_goal_id : Nat) (IT : IntroTree UInt32Array):=
  @IntroTree.mergeLtxForGoalId
    UInt32Array MetaM _ _
    (fun x y => y.oContains x.toUInt32) UInt32Array.union UInt32Array.empty
    target_goal_id IT .dead


#check 1
#check IntroTree.insertGoalsAtGoalId



def mergeLtxForGoalIdTruelyS (target_goal_id : Nat) (IT : IntroTree UInt32Array):=
  @IntroTree.mergeLtxForGoalIdTruely
    UInt32Array MetaM _ _
    (fun x y => y.oContains x.toUInt32) UInt32Array.union UInt32Array.empty
    target_goal_id IT .dead


#check 1
#check IntroTree.insertGoalsAtGoalId



def IntroTree.insertGoalsAtGoalIdS :=
  @IntroTree.insertGoalsAtGoalId UInt32Array _ _
    (fun x y => y.oContains x.toUInt32) UInt32Array.union
    (fun x => UInt32Array.single x.toUInt32) UInt32Array.empty
    (fun x y => y.oInsert x.toUInt32)


#check 1


def IntroTree.addBackStep (l1 : LocalContext)
  (target_goal_id savedGoalId : Nat) (backTypes : Array Expr) (IT : IntroTree UInt32Array)
  : MetaM (Prod (IntroTree UInt32Array) LocalContext) := do
  let target_goal ← IT.getGoalOfGoalId (fun x y => y.oContains x.toUInt32)
    UInt32Array.isEmpty UInt32Array.inter (fun x => UInt32Array.single x.toUInt32)
    l1 target_goal_id -- akward
  let newGoals : ListProd Nat Expr := (List.range backTypes.size).foldl (fun R i =>
    .cons (savedGoalId + i) backTypes[i]! R
    ) (ListProd.cons (savedGoalId + backTypes.size) target_goal .nil) -- because at `BackTree.addBackStep`, propa will have save type as initial goal
  IT.insertGoalsAtGoalIdS l1 target_goal_id newGoals

#check 1

def potentialFixHelp (A : Array (OptionProd Nat Nat)) (backId tnodeRange : Nat) : Array (OptionProd Nat Nat) :=
  tnodeRange.fold (fun i _ A => A.push (.some backId i)) A


/--
todo from here :
- for goal ids passed in continuation, add to ranking system, ie. find applicables and their scores
-/
def integrateBackwardStd (l1 : LocalContext) (l2 : LocalInstances) (revCountMax : Nat)
  (target_goal_id : Nat) (term : Expr) (metadata : BackStepMetadata) (tnodeRange : Nat)
  (ta : ListProd3 Nat Nat Expr) (la : ListProd3 Nat Nat Level)
  (st : SearchState UInt32Array)
  : MetaM (Prod5 (ListProd3 Nat FVarId Expr) (ListProd Nat Expr) (SearchState UInt32Array) LocalContext LocalInstances) :=
  do
  mtracing
  let ltxPaIn ← mergeLtxForGoalIdTruelyS target_goal_id st.introTree
  mtrace on .one with s!"[integrateBackwardStd] ltxPaIn{← ltxPaIn.ppS l1 l2 [] 0}"
  let st := {st with id_gen_back := st.id_gen_back + 1}
  let mut mst := st
  for _ in [:(tnodeRange + 1)] do -- +1 to account for the ofPropa on top of the backstep at `addBackstep`
    mst := {mst with goalHeights := updateGoalHeight mst.goalHeights target_goal_id}
    mst := {mst with backDepths := updateBackDepth mst.backDepths target_goal_id}
  let st := mst
  mtrace on .one with s!"[integrateBackwardStd] new goalHeights {st.goalHeights}"
  mtrace on .one with s!"[integrateBackwardStd] new backDepths {st.backDepths.map (fun x => x.depth)}"
  --let spb := st.goalSpawn[target_goal_id]!
  --let st := {st with goalSpawn := st.goalSpawn.pushN spb (tnodeRange + 1)} -- +1 to account for the ofPropa on top of the backstep at `addBackstep`
  let st := {st with goalSpawn := potentialFixHelp st.goalSpawn (st.id_gen_back - 1) (tnodeRange + 1)}
  mtrace on .one with s!"[integrateBackwardStd] new goalSpawn {repr st.goalSpawn}"
  let .mk ta l1 l2 ← ta.foldlM ((.mk ListProd3.nil l1 l2) : Prod3 (ListProd3 Nat Nat Expr) _ _) (fun x y z (.mk R l1 l2) => do
    let .mk z l1 l2 ← mvarifyTnodesRec z l1 l2
    return .mk (.cons x y z R) l1 l2)
  let .mk la l1 l2 ← la.foldlM ((.mk ListProd3.nil l1 l2) : Prod3 (ListProd3 Nat Nat Level) _ _) (fun x y z (.mk R l1 l2) => do
    let .mk z l1 l2 ← mvarifyLTnodesIn z l1 l2
    return .mk (.cons x y z R) l1 l2)
  let st ← computeNewClashesMain l1 l2 st ta la
  let backTypes : Array Expr := ← (Array.range tnodeRange).mapM (fun i => do
    let tn := tnode (st.id_gen_back - 1) i ; (⟨tn⟩ : FVarId).GetType l1 l2)
  let save := st.id_gen_goal
  let (idgg,bt) :=
    st.backTree.addBackstep
      st.id_gen_apass target_goal_id st.id_gen_goal (st.id_gen_back - 1)
      tnodeRange (.single (st.id_gen_uni - 1).toUInt32) backTypes metadata term
  mtrace on .one with s!"[integrateBackwardStd] backtree after addBackstep {← bt.pp 0}"
  let st := {st with id_gen_goal := idgg + 1, backTree := bt} -- +1 to account for the ofPropa on top of the backstep at `addBackstep` ; very akward ... id_gen_goal only increases by exactly (tnodeRange+1)
  let .mk IT l1 ←  st.introTree.addBackStep l1 target_goal_id save backTypes
  mtrace on .one with s!"[integrateBackwardStd] backtree after addBackstep {IT.pp 0}"
  let st := {st with introTree := IT}
  let st := {st with backTree := st.backTree.addUnis st.id_gen_apass (.single (st.id_gen_uni - 1).toUInt32) ta}
  mtrace on .one with s!"[integrateBackwardStd] backtree after addUnis {← st.backTree.pp 0}"
  (List.range tnodeRange).foldlMcps ((.mk st (.nil : ListProd3 Nat Expr (PaInG UInt32Array)) (.nil : ListProd3 Nat FVarId Expr) l1 l2) : Prod5 _ _ _ _ _ ) (fun i (.mk st introNewGs introFs l1 l2) q => do
    mtrace on .one with s!"[integrateBackwardStd] introing new goal correpsonding to {i}th arg of backstep"
    let BT ← WhnfR (backTypes[i]!) l1 l2
    mtrace on .one with s!"[integrateBackwardStd] cleaned goal type to {← ppExpr BT}"
    let .mk introFs introNewGs st l1 l2 ← introWiLtxMain l1 l2
      st introNewGs introFs (save + i) BT ltxPaIn
        --q (st, introNewGs, introFs)
    q <| .mk st (ListProd3.cons (save + i) BT ltxPaIn introNewGs) introFs l1 l2)
      <| fun (.mk st introNewGs introFs l1 l2) => do
      mtrace on .one with s!"[integrateBackwardStd] after intro, new goals {← introNewGs.foldlM ListProd.nil (fun x y _ z => return .cons x (← ppExpr y) z)}"
      introNewGs.foldlMcps (.mk st l1 l2 : Prod3 _ _ _) (fun gi ge lP (.mk st l1 l2) q => do
        let ge ← WhnfR ge l1 l2 -- needed again since whnf doesn't reduce under binders, that have now been introed
        mtrace on .one with s!"[integrateBackwardStd] unifying goal {gi} ot type {← ppExpr ge} wrt. {← lP.ppS l1 l2 [] 0 }"
        let .mk yes? _ unifs l1 l2 ← uniBEwFTMainS l1 l2
          lP.getIndicesS revCountMax ge lP
        if yes? != 3
        then
          mtrace on .zero with s!"[integrateBackwardStd] uniBEwFTMainS fail"
          q (.mk st l1 l2)
        else
          mtrace on .zero with s!"[integrateBackwardStd] uniBEwFTMainS success with unifs {unifs} "-- {unifs.foldl [] (fun x _ _ R => x :: R)}
          let .mk st l1 l2 ← unifs.foldlM (.mk st l1 l2 : Prod3 _ _ _) (fun forwInds ta la (.mk st l1 l2) => do
            let .mk ta l1 l2 ← ta.foldlM ((.mk ListProd3.nil l1 l2) : Prod3 (ListProd3 Nat Nat Expr) _ _) (fun x y z (.mk R l1 l2) => do
              let .mk z l1 l2 ← mvarifyTnodesRec z l1 l2
              return .mk (.cons x y z R) l1 l2)
            let .mk la l1 l2 ← la.foldlM ((.mk ListProd3.nil l1 l2) : Prod3 (ListProd3 Nat Nat Level) _ _) (fun x y z (.mk R l1 l2) => do
              let .mk z l1 l2 ← mvarifyLTnodesIn z l1 l2
              return .mk (.cons x y z R) l1 l2)
            let st ← forwInds.foldlM st (fun foId st => do
              let foId := foId.toNat
              match st.goalSpawn[gi]! with
              | .some b p =>
                  mtrace on .zero with s!" adding backstep {b} {p} to ta"
                  let name := if st.uNodes.contains foId then unode foId else gnode foId
                  let ta := ListProd3.cons b p (.fvar ⟨name⟩) ta
                  let st ← computeNewClashesMain l1 l2 st ta la -- bumps id_gen_uni
                  mtrace on .zero with s!" clashes {st.unif_claches.toListOfProd}"
                  let st := {st with backTree := st.backTree.addUnis st.id_gen_apass (.single (st.id_gen_uni - 1).toUInt32) ta}
                  mtrace on .three with s!" sanity {st.backTree.ppDirs 0}"
                  return st
              | .none =>
                  let st ← computeNewClashesMain l1 l2 st ta la -- bumps id_gen_uni
                  mtrace on .zero with s!" clashes {st.unif_claches.toListOfProd}"
                  let st := {st with backTree := st.backTree.addUnis st.id_gen_apass (.single (st.id_gen_uni - 1).toUInt32) ta}
                  mtrace on .three with s!" sanity {st.backTree.ppDirs 0}"
                  return st
              )
            return (.mk st l1 l2)
            )
          mtrace on .zero with s!"[integrateBackwardStd] backTree : {← st.backTree.pp 0}"
          q (.mk st l1 l2)
        ) <| fun (.mk st l1 l2) => do
          let newGs := introNewGs.foldl .nil (fun x y _ r => .cons x y r)
          return .mk introFs newGs st l1 l2

#check 1


#check IntroTree.insertGoalsAtGoalId
#check BackTree.addUnis



#check 1

def integratePropaedGoalStd (l1 : LocalContext) (l2 : LocalInstances) (revCountMax : Nat)
  (target_goal_id : Nat) (type : Expr) (st : SearchState UInt32Array)
  : MetaM (Prod5 (ListProd3 Nat FVarId Expr) (ListProd Nat Expr) (SearchState UInt32Array) LocalContext LocalInstances) :=
  do
  mtracing
  let ltxPaIn ← mergeLtxForGoalIdTruelyS target_goal_id st.introTree
  mtrace on .one with s!"[integratePropaedGoalStd] ltxPaIn {← ltxPaIn.ppS l1 l2 [] 0}"
  let st := {st with goalHeights := updateGoalHeight st.goalHeights target_goal_id}
  let st := {st with backDepths := updateBackDepth st.backDepths target_goal_id}
  mtrace on .one with s!"[integratePropaedGoalStd] new goalHeights {st.goalHeights}"
  mtrace on .one with s!"[integratePropaedGoalStd] new backDepths {st.backDepths.map (fun x => x.depth)}"
  -- *Note* `goalSpawn` has already been handled at `BackTree.propagateForBackAssembly`
  let type ← WhnfR type l1 l2
  mtrace on .one with s!"[integratePropaedGoalStd] cleaned goal type to {← ppExpr type}"
  let .mk introFs introNewGs st l1 l2 ← introWiLtxMain l1 l2
    st .nil .nil target_goal_id type ltxPaIn
  mtrace on .one with s!"[integratePropaedGoalStd] after intro, new goals {← introNewGs.foldlM ListProd.nil (fun x y _ z => return .cons x (← ppExpr y) z)}"
  introNewGs.foldlMcps (.mk st l1 l2 : Prod3 _ _ _) (fun gi ge lP (.mk st l1 l2) q => do
    mtrace on .one with s!"[integratePropaedGoalStd] unifying goal {gi} ot type {← ppExpr ge}"
    let .mk yes?  _ unifs l1 l2 ← uniBEwFTMainS l1 l2
      lP.getIndicesS revCountMax ge lP
    if yes? != 3
    then
      mtrace on .zero with s!"[integratePropaedGoalStd] uniBEwFTMainS fail"
      q (.mk st l1 l2)
    else
      let st ← unifs.foldlM st (fun forwInds ta la st => do
        let .mk ta l1 l2 ← ta.foldlM ((.mk ListProd3.nil l1 l2) : Prod3 (ListProd3 Nat Nat Expr) _ _) (fun x y z (.mk R l1 l2) => do
          let .mk z l1 l2 ← mvarifyTnodesRec z l1 l2
          return .mk (.cons x y z R) l1 l2)
        let .mk la l1 l2 ← la.foldlM ((.mk ListProd3.nil l1 l2) : Prod3 (ListProd3 Nat Nat Level) _ _) (fun x y z (.mk R l1 l2) => do
          let .mk z l1 l2 ← mvarifyLTnodesIn z l1 l2
          return .mk (.cons x y z R) l1 l2)
        let st ← forwInds.foldlM st (fun foId st => do
          let foId := foId.toNat
          match st.goalSpawn[gi]! with
          | .some b p =>
              let name := if st.uNodes.contains foId then unode foId else gnode foId
              let ta := ListProd3.cons b p (.fvar ⟨name⟩) ta
              let st ← computeNewClashesMain l1 l2 st ta la -- bumps id_gen_uni
              let st := {st with backTree := st.backTree.addUnis st.id_gen_apass (.single (st.id_gen_uni - 1).toUInt32) ta}
              return st
          | .none =>
              let st ← computeNewClashesMain l1 l2 st ta la -- bumps id_gen_uni
              let st := {st with backTree := st.backTree.addUnis st.id_gen_apass (.single (st.id_gen_uni - 1).toUInt32) ta}
              return st
          )
        return st
        )
      mtrace on .zero with s!"[integratePropaedGoalStd] backTree : {← st.backTree.pp 0}"
      q (.mk st l1 l2)
    ) <| fun (.mk st l1 l2) => do
      let newGs := introNewGs.foldl .nil (fun x y _ r => .cons x y r)
      return .mk introFs newGs st l1 l2

#check 1


/-- like `integratePropaedGoalStd`, but no height and depth bump -/
def integrateInitialGoal (l1 : LocalContext) (l2 : LocalInstances) (revCountMax : Nat)
  (target_goal_id : Nat) (type : Expr)
  (st : SearchState UInt32Array)
  : MetaM (Prod5 (ListProd3 Nat FVarId Expr) (ListProd Nat Expr) (SearchState UInt32Array) LocalContext LocalInstances) :=
  do
  mtracing
  let ltxPaIn ← mergeLtxForGoalIdTruelyS target_goal_id st.introTree
  mtrace on .one with s!"[integrateInitialGoal] ltxPaIn {← ltxPaIn.ppS l1 l2 [] 0}"
  let type ← WhnfR type l1 l2
  mtrace on .one with s!"[integrateInitialGoal] cleaned goal type to {← ppExpr type}"
  let .mk introFs introNewGs st l1 l2 ← introWiLtxMain l1 l2
    st .nil .nil target_goal_id type ltxPaIn
  mtrace on .one with s!"[integrateInitialGoal] after intro, new goals {← introNewGs.foldlM ListProd.nil (fun x y _ z => return .cons x (← ppExpr y) z)}"
  introNewGs.foldlMcps ((.mk st l1 l2) : Prod3 _ _ _) (fun gi ge lP (.mk st l1 l2) q => do
    mtrace on .one with s!"[integrateInitialGoal] unifying goal {gi} ot type {← ppExpr ge}"
    let .mk yes?  _ unifs l1 l2 ← uniBEwFTMainS l1 l2
      lP.getIndicesS revCountMax ge lP
    if yes? != 3
    then
      mtrace on .zero with s!"[integrateInitialGoal] uniBEwFTMainS fail"
      q (.mk st l1 l2)
    else
      let (.mk st l1 l2) ← unifs.foldlM ((.mk st l1 l2) : Prod3 _ _ _) (fun forwInds ta la (.mk st l1 l2) => do
        let .mk ta l1 l2 ← ta.foldlM ((.mk ListProd3.nil l1 l2) : Prod3 (ListProd3 Nat Nat Expr) _ _) (fun x y z (.mk R l1 l2) => do
          let .mk z l1 l2 ← mvarifyTnodesRec z l1 l2
          return .mk (.cons x y z R) l1 l2)
        let .mk la l1 l2 ← la.foldlM ((.mk ListProd3.nil l1 l2) : Prod3 (ListProd3 Nat Nat Level) _ _) (fun x y z (.mk R l1 l2) => do
          let .mk z l1 l2 ← mvarifyLTnodesIn z l1 l2
          return .mk (.cons x y z R) l1 l2)
        let st ← forwInds.foldlM st (fun foId st => do
          let foId := foId.toNat
          match st.goalSpawn[gi]! with
          | .some b p =>
              let name := if st.uNodes.contains foId then unode foId else gnode foId
              let ta := ListProd3.cons b p (.fvar ⟨name⟩) ta
              let st ← computeNewClashesMain l1 l2 st ta la -- bumps id_gen_uni
              let st := {st with backTree := st.backTree.addUnis st.id_gen_apass (.single (st.id_gen_uni - 1).toUInt32) ta}
              return st
          | .none =>
              let st ← computeNewClashesMain l1 l2 st ta la -- bumps id_gen_uni
              let st := {st with backTree := st.backTree.addUnis st.id_gen_apass (.single (st.id_gen_uni - 1).toUInt32) ta}
              return st
          )
        return (.mk st l1 l2)
        )
      mtrace on .zero with s!"[integrateInitialGoal] backTree : {← st.backTree.pp 0}"
      q (.mk st l1 l2)
    ) <| fun (.mk st l1 l2) => do
      let newGs := introNewGs.foldl .nil (fun x y _ r => .cons x y r)
      return .mk introFs newGs st l1 l2
