/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrowBeta.Search.API.IntegrateBack
import LeanGrowBeta.Search.API.ScoreCore
import LeanGrowBeta.Core.GeneralisePaIn.Subpattern


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

#check genQuerySubpat



def genQuerySubpatS (l1 : LocalContext)
  (l2 : LocalInstances) (revCountMax : Nat) (toLoad : Array loadDataType) (T : PaIn (List Nat)) (weights : Array Float)
  (e : Expr): MetaM (Prod3 Float LocalContext LocalInstances) :=
  @genQuerySubpat (List Nat) _ _ _ id
    List.isEmpty (List.orderedIntersect) (List.orderedUnion) []
    l1 l2 revCountMax toLoad T weights e


#check 1



def addBackCandOfInductGoal (l1 : LocalContext) (l2 : LocalInstances) (cfg : SearchConfig) (st : SearchState (List Nat))
  (target_goal_id : Nat) (target_goal_type : Expr)
  : MetaM (Prod3 (SearchState (List Nat)) LocalContext LocalInstances) :=
  do -- trace set Tracing.Flags.none in do
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
      match cfg.recuSubpatternScores.find? name.toString.toUTF8 with
      | .none => panic s!"[addBackCandOfInductGoal] no score data found for {name}"
      | .some subPats =>
          let .mk score l1 l2 ← genQuerySubpatS l1 l2 cfg.revCountMax subPats.loadData subPats.pi subPats.weights target_goal_type
          mtrace on .one with s!"[addBackCandOfInductGoal] absolut score {score}"
          let score := score / subPats.totalWeight
          mtrace on .one with s!"[addBackCandOfInductGoal] looking at {score}"
          let st := {st with id_gen_cand := st.id_gen_cand + 1, inductCandScores := .cons st.id_gen_cand cfg.default_relevance_timer tar target_goal_id target_goal_type score st.inductCandScores}
          q (.mk st l1 l2)
    ) (fun x => return x)


def addBackCandOfInductForw (l1 : LocalContext) (l2 : LocalInstances)  (cfg : SearchConfig) (st : SearchState (List Nat))
  (target_forw_id : Nat)
  : MetaM (Prod3 (SearchState (List Nat)) LocalContext LocalInstances) :=
  do -- trace set Tracing.Flags.none in do
  let fvid : FVarId := if st.uNodes.binSearchContains target_forw_id (· < ·) then ⟨unode target_forw_id⟩ else ⟨gnode target_forw_id⟩
  let .mk tars l1 l2 ← detectIndHyp l1 l2 cfg.funrecus cfg.elimrecus fvid
  let (target_goal_id, target_goal_type) := st.introTree.topGoalForForwId target_forw_id
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
      match cfg.recuSubpatternScores.find? name.toString.toUTF8 with
      | .none => panic s!"[addBackCandOfInductForw] no score data found for {name}"
      | .some subPats =>
          let .mk score l1 l2 ← genQuerySubpatS l1 l2 cfg.revCountMax subPats.loadData subPats.pi subPats.weights target_goal_type
          mtrace on .one with s!"[addBackCandOfInductForw] absolut score {score}"
          let score := score / subPats.totalWeight
          mtrace on .one with s!"[addBackCandOfInductForw] looking at {score}"
          let st := {st with id_gen_cand := st.id_gen_cand + 1, inductCandScores := .cons st.id_gen_cand cfg.default_relevance_timer tar target_goal_id target_goal_type score st.inductCandScores}
          q (.mk st l1 l2)
    ) (fun x => return x)


-- for inductions ↓
#check inductiveInductionData
#check functionalInductionData
-- In ↓, size of subgoal array correponds to tnodeRange
#check elimInductionData


-- ↓ + its docs suggestions
#check integrateBackwardStd


def integrateInduction (l1 : LocalContext) (l2 : LocalInstances)
  (cfg : SearchConfig) (st : SearchState (List Nat))
  (tar : TargetType) (target_goal_id : Nat) (target_goal_type : Expr)
  : MetaM (Prod3 (SearchState (List Nat)) LocalContext LocalInstances) :=
  do -- trace set Tracing.Flags.none in do
  let introAd := st.introTree.gatherUGidsToGoalId target_goal_id []
  let admi := fun n : Nat => introAd.orderedContains n
  match tar with
  | .indu major =>
      let mT ← Whnf (← InferType major l1 l2) l1 l2
      let .const n .. := mT.getAppFn | throwError s!"[integrateInduction] major type isn't constant headed {← ppExpr mT}"
      let .mk r l1 l2 ← inductiveInductionData
        admi st.depsCache #[] cfg.sinkRevCutOff l1 l2 st.id_gen_back
        major target_goal_type
      match r with
      | .none => return .mk {st with id_gen_back := st.id_gen_back + 1} l1 l2 -- don't know if bump is necessary ?
      | .some term subgs =>
          mtrace on .one with s!"[integrateInduction] built term : {← ppExpr term}"
          let .mk nIs nGs st l1 l2 ← integrateBackwardStd l1 l2 cfg.revCountMax target_goal_id term
            (.recu n.toString)
            subgs.size .nil .nil st
          mtrace on .one with s!"[integrateInduction] adding to cycleAddBack : {← nGs.foldlM ListProd.nil (fun x y z => return .cons x (← ppExpr y) z)}"
          mtrace on .one with s!"[integrateInduction] adding to cycleAddForw : {← nIs.foldlM ListProd.nil (fun x y z => return .cons x (← ppExpr y) z)}"
          let st := {st with cycleAddForw := nIs.append st.cycleAddForw, cycleAddBack := nGs.append st.cycleAddBack}
          return .mk st l1 l2
  | .func targets recu =>
      let .mk r l1 l2 ← functionalInductionData
        admi st.depsCache #[] cfg.sinkRevCutOff l1 l2 st.id_gen_back
        target_goal_type targets recu
      match r with
      | .none => return .mk {st with id_gen_back := st.id_gen_back + 1} l1 l2 -- don't know if bump is necessary ?
      | .some term subgs =>
          mtrace on .one with s!"[integrateInduction] built term : {← ppExpr term}"
          let .mk nIs nGs st l1 l2 ← integrateBackwardStd l1 l2 cfg.revCountMax target_goal_id term
            (.recu recu.name.toString)
            subgs .nil .nil st
          mtrace on .one with s!"[integrateInduction] adding to cycleAddBack : {← nGs.foldlM ListProd.nil (fun x y z => return .cons x (← ppExpr y) z)}"
          mtrace on .one with s!"[integrateInduction] adding to cycleAddForw : {← nIs.foldlM ListProd.nil (fun x y z => return .cons x (← ppExpr y) z)}"
          let st := {st with cycleAddForw := nIs.append st.cycleAddForw, cycleAddBack := nGs.append st.cycleAddBack}
          return .mk st l1 l2
  | .elim targets recu =>
      let .mk r l1 l2 ← elimInductionData
        admi st.depsCache #[] cfg.sinkRevCutOff l1 l2 st.id_gen_back
        target_goal_type targets recu
      match r with
      | .none => return .mk {st with id_gen_back := st.id_gen_back + 1} l1 l2 -- don't know if bump is necessary ?
      | .some term subgs =>
          mtrace on .one with s!"[integrateInduction] built term : {← ppExpr term}"
          let .mk nIs nGs st l1 l2 ← integrateBackwardStd l1 l2 cfg.revCountMax target_goal_id term
            (.recu recu.name.toString)
            subgs .nil .nil st
          mtrace on .one with s!"[integrateInduction] adding to cycleAddBack : {← nGs.foldlM ListProd.nil (fun x y z => return .cons x (← ppExpr y) z)}"
          mtrace on .one with s!"[integrateInduction] adding to cycleAddForw : {← nIs.foldlM ListProd.nil (fun x y z => return .cons x (← ppExpr y) z)}"
          let st := {st with cycleAddForw := nIs.append st.cycleAddForw, cycleAddBack := nGs.append st.cycleAddBack}
          return .mk st l1 l2
