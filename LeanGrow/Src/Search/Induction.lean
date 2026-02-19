/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Search.API.IntegrateBack
import LeanGrow.Src.Search.API.ScoreCore
import LeanGrow.Src.SampleGenScore.Gen.Subpattern


open Lean Meta

-- also, get inductions (don't forget to reduce instances ! ; or is it done in ↓)
#check detectIndGoal

#print TargetType
#print RecursorCache
#print FunRecursorCache

#check detectIndHyp
-- and find most general goal to perform induction on via
#check IntroTree.topGoalForForwId
-- these unduction will be handled the same as the backwards case

#check PaIn.genQueryBackSubpatMain



def genQuerySubpatS (l1 : LocalContext)
  (l2 : LocalInstances) (constr : UInt32Array) (revCountMax : Nat)  (T : PaIn UInt32Array)
  (e : Expr): MetaM (Prod3 UInt32Array LocalContext LocalInstances) :=
  PaIn.genQueryBackSubpatMain
    UInt32Array.isEmpty UInt32Array.inter UInt32Array.union UInt32Array.empty
    l1 l2 constr revCountMax e T


#check 1



def addBackCandOfInductGoal (l1 : LocalContext) (l2 : LocalInstances) (cfg : SearchConfig UInt32Array) (st : SearchState UInt32Array)
  (target_goal_id : Nat) (target_goal_type : Expr)
  : MetaM (Prod3 (SearchState UInt32Array) LocalContext LocalInstances) :=
  do
  mtracing
  let .mk tars l1 l2 ← detectIndGoal l1 l2 cfg.funrecus cfg.elimrecus target_goal_type
  mtrace on .one with s!"[addBackCandOfInductGoal] found targets {repr tars}"
  tars.foldlMcps (.mk st l1 l2) (fun tar (.mk st l1 l2) q => do
    let name : Name := ← do
      match tar with
      | .indu major =>
          let .const n _ := (← WhnfAtMostI (← InferType major l1 l2) l1 l2).getAppFn | (panic s!"[addBackCandOfInductGoal] major type isn't constant headed: {← ppExpr <| ← inferType major}")
          return n
      | .func _ d => return d.name
      | .elim _ d => return d.name
    mtrace on .one with s!"[addBackCandOfInductGoal] looking at {name}"
    if cfg.sandboxMode
    then
      let st := {st with id_gen_cand := st.id_gen_cand + 1, inductCandScores := .cons st.id_gen_cand cfg.default_relevance_timer tar target_goal_id target_goal_type cfg.sandboxModThmScore st.inductCandScores}
      q (.mk st l1 l2)
    else
      match cfg.subpat.find? name.toString.toUTF8 with
      | .none => panic s!"[addBackCandOfInductGoal] no score data found for {name}"
      | .some (.mk subPats weights totalWeight) =>
          let .mk score l1 l2 ← genQuerySubpatS l1 l2 subPats.getIndicesS cfg.revCountMax subPats target_goal_type
          let score := score.foldl 0 (fun i r => weights[i.toNat]! + r)
          mtrace on .one with s!"[addBackCandOfInductGoal] absolut score {score}"
          let score := score.toFloat / totalWeight.toFloat
          mtrace on .one with s!"[addBackCandOfInductGoal] looking at {score}"
          let st := {st with id_gen_cand := st.id_gen_cand + 1, inductCandScores := .cons st.id_gen_cand cfg.default_relevance_timer tar target_goal_id target_goal_type score st.inductCandScores}
          q (.mk st l1 l2)
    ) (fun x => return x)



def addBackCandOfInductForw (l1 : LocalContext) (l2 : LocalInstances)  (cfg : SearchConfig UInt32Array) (st : SearchState UInt32Array)
  (target_forw_id : Nat)
  : MetaM (Prod3 (SearchState UInt32Array) LocalContext LocalInstances) :=
  do
  mtracing
  let fvid : FVarId := if st.uNodes.binSearchContains target_forw_id (· < ·) then ⟨unode target_forw_id⟩ else ⟨gnode target_forw_id⟩
  let .mk tars l1 l2 ← detectIndHyp l1 l2 cfg.funrecus cfg.elimrecus fvid
  let .mk target_goal_id target_goal_type l1 ← st.introTree.topGoalForForwId
    (fun x y => y.oContains x.toUInt32) UInt32Array.isEmpty UInt32Array.inter
    (fun x => .single x.toUInt32) (fun x => x[0]!.toNat)
    l1 target_forw_id
  -- ↓ identical to `addBackCandOfInductGoal`
  mtrace on .one with s!"[addBackCandOfInductForw] found targets {repr tars}"
  tars.foldlMcps (.mk st l1 l2) (fun tar (.mk st l1 l2) q => do
    let name : Name := ← do
      match tar with
      | .indu major =>
          let .const n _ := (← WhnfAtMostI (← InferType major l1 l2) l1 l2).getAppFn | (panic s!"[addBackCandOfInductForw] major type isn't constant headed: {← ppExpr <| ← inferType major}")
          return n
      | .func _ d => return d.name
      | .elim _ d => return d.name
    mtrace on .one with s!"[addBackCandOfInductForw] looking at {name}"
    if cfg.sandboxMode
    then
      let st := {st with id_gen_cand := st.id_gen_cand + 1, inductCandScores := .cons st.id_gen_cand cfg.default_relevance_timer tar target_goal_id target_goal_type cfg.sandboxModThmScore st.inductCandScores}
      q (.mk st l1 l2)
    else
      match cfg.subpat.find? name.toString.toUTF8 with
      | .none => panic s!"[addBackCandOfInductForw] no score data found for {name}"
      | .some (.mk subPats weights totalWeight) =>
          let .mk score l1 l2 ← genQuerySubpatS l1 l2 subPats.getIndicesS cfg.revCountMax subPats target_goal_type
          let score := score.foldl 0 (fun i r => weights[i.toNat]! + r)
          mtrace on .one with s!"[addBackCandOfInductGoal] absolut score {score}"
          let score := score.toFloat / totalWeight.toFloat
          mtrace on .one with s!"[addBackCandOfInductForw] looking at {score}"
          let st := {st with id_gen_cand := st.id_gen_cand + 1, inductCandScores := .cons st.id_gen_cand cfg.default_relevance_timer tar target_goal_id target_goal_type score st.inductCandScores}
          q (.mk st l1 l2)
    ) (fun x => return x)


#check inductiveInductionMain



def integrateInduction (l1 : LocalContext) (l2 : LocalInstances)
  (cfg : SearchConfig UInt32Array) (st : SearchState UInt32Array)
  (tar : TargetType) (target_goal_id : Nat) (target_goal_type : Expr)
  : MetaM (Prod3 (SearchState UInt32Array) LocalContext LocalInstances) :=
  do
  mtracing
  let introAd := st.introTree.gatherUGidsToGoalId
    (fun x y => y.oContains x.toUInt32) UInt32Array.union
    target_goal_id .empty
  let admi := fun n : Nat => introAd.oContains n.toUInt32
  match tar with
  | .indu major =>
      let mT ← Whnf (← InferType major l1 l2) l1 l2
      let .const n .. := mT.getAppFn | throwError s!"[integrateInduction] major type isn't constant headed {← ppExpr mT}"
      let .mk r l1 l2 ← inductiveInductionMain
        admi cfg.sinkRevCutOff st.depsCache l1 l2 st.id_gen_back
        major target_goal_type
      match r with
      | .none => return .mk {st with id_gen_back := st.id_gen_back + 1} l1 l2 -- don't know if bump is necessary ?
      | .some term subgs =>
          mtrace on .one with s!"[integrateInduction] built term : {← ppExpr term}"
          let .mk nIs nGs st l1 l2 ← integrateBackwardStd l1 l2 cfg.revCountMax target_goal_id term
            (.recu n.toString)
            subgs.size .nil .nil st
          mtrace on .one with s!"[integrateInduction] adding to cycleAddBack : {← nGs.foldlM ListProd.nil (fun x y z => return .cons x (← ppExpr y) z)}"
          mtrace on .one with s!"[integrateInduction] adding to cycleAddForw : {← nIs.foldlM ListProd.nil (fun x _ y z => return .cons x (← ppExpr y) z)}"
          let st := {st with cycleAddForw := nIs.append st.cycleAddForw, cycleAddBack := nGs.append st.cycleAddBack}
          return .mk st l1 l2
  | .func targets recu =>
      let .mk r l1 l2 ← functionalInductionMain
        admi cfg.sinkRevCutOff st.depsCache  l1 l2 st.id_gen_back
        target_goal_type targets recu
      match r with
      | .none => return .mk {st with id_gen_back := st.id_gen_back + 1} l1 l2 -- don't know if bump is necessary ?
      | .some term subgs =>
          mtrace on .one with s!"[integrateInduction] built term : {← ppExpr term}"
          let .mk nIs nGs st l1 l2 ← integrateBackwardStd l1 l2 cfg.revCountMax target_goal_id term
            (.recu recu.name.toString)
            subgs .nil .nil st
          mtrace on .one with s!"[integrateInduction] adding to cycleAddBack : {← nGs.foldlM ListProd.nil (fun x y z => return .cons x (← ppExpr y) z)}"
          mtrace on .one with s!"[integrateInduction] adding to cycleAddForw : {← nIs.foldlM ListProd.nil (fun x _ y z => return .cons x (← ppExpr y) z)}"
          let st := {st with cycleAddForw := nIs.append st.cycleAddForw, cycleAddBack := nGs.append st.cycleAddBack}
          return .mk st l1 l2
  | .elim targets recu =>
      let .mk r l1 l2 ← elimInductionMain
        admi cfg.sinkRevCutOff st.depsCache l1 l2 st.id_gen_back
        target_goal_type targets recu
      match r with
      | .none => return .mk {st with id_gen_back := st.id_gen_back + 1} l1 l2 -- don't know if bump is necessary ?
      | .some term subgs =>
          mtrace on .one with s!"[integrateInduction] built term : {← ppExpr term}"
          let .mk nIs nGs st l1 l2 ← integrateBackwardStd l1 l2 cfg.revCountMax target_goal_id term
            (.recu recu.name.toString)
            subgs .nil .nil st
          mtrace on .one with s!"[integrateInduction] adding to cycleAddBack : {← nGs.foldlM ListProd.nil (fun x y z => return .cons x (← ppExpr y) z)}"
          mtrace on .one with s!"[integrateInduction] adding to cycleAddForw : {← nIs.foldlM ListProd.nil (fun x _ y z => return .cons x (← ppExpr y) z)}"
          let st := {st with cycleAddForw := nIs.append st.cycleAddForw, cycleAddBack := nGs.append st.cycleAddBack}
          return .mk st l1 l2
