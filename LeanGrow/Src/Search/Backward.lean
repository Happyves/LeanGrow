
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrowBeta.Search.API.IntegrateBack
import LeanGrowBeta.Core.Embedding.EmbedProcessBack
import LeanGrowBeta.Core.Embedding.EmbedQueryBack
import LeanGrowBeta.Search.API.ScoreCore


open Lean Meta


-- Query with
#check PaIn.embedBackMain


def PaIn.embedBackMainS
  (l1 : LocalContext) (l2 : LocalInstances) (thmData : CTrie (Array ThmFormat)) :=
    @PaIn.embedBackMain (List Nat) l1 l2 thmData _ _
    List.isEmpty List.orderedIntersect List.orderedUnion List.orderedDiff []


#check embedBackRWMain

def addBackCandOfStd (l1 : LocalContext) (l2 : LocalInstances)
  (cfg : SearchConfig) (st : SearchState (List Nat))
  (target_goal_id : Nat) (target_goal_type : Expr)
  : MetaM (Prod3 (SearchState (List Nat)) LocalContext LocalInstances) :=
  do --trace set Tracing.Flags.none in do
  let .mk yes? _ embs l1 l2 ← st.stdBackPaIn.embedBackMainS l1 l2
    st.thmData st.stdBackPaIn.getIndicesS cfg.revCountMax [] target_goal_type
  if yes? != 3
  then
    mtrace on .one with s!"[addBackCandOfStd] embedBackMainS failed"
    return .mk st l1 l2
  else
    embs.foldlMcps (.mk (.nil : ListProd5 Nat BackCandData Nat ScoreType (List (CSetTrie (List Nat) Nat))) st.id_gen_cand l1 l2 : Prod4 _ _ _ _) (fun thmInds embData (.mk cand igc l1 l2) q0 => do
      do
      mtrace on .one with s!"[addBackCandOfStd] looking at embedding (ln) {← embData.ln.foldlM ListProd.nil (fun x y z => return .cons x (← ppExpr y) z)}"
      mtrace on .one with s!"[addBackCandOfStd] looking at embedding (tn) {← embData.tn.foldlM ListProd3.nil (fun x w y z => return .cons x w (← ppExpr y) z)}"
      thmInds.foldlMcps (.mk cand igc l1 l2 : Prod4 _ _ _ _) (fun i (.mk cand igc l1 l2) q1 => do
        mtrace on .one with s!"[addBackCandOfStd] igc {igc}"
        let thm := st.thm_data[i]!
        mtrace on .one with s!"[addBackCandOfStd] looking at thm {repr thm.name}"
        let .mk ta l1 l2 ← embData.tn.foldlM ((.mk ListProd3.nil l1 l2) : Prod3 (ListProd3 Nat Nat Expr) _ _) (fun x y z (.mk R l1 l2) => do
          let .mk z l1 l2 ← mvarifyTnodesRecWiContextIn z l1 l2
          return .mk (.cons x y z R) l1 l2)
        let .mk la l1 l2 ← embData.tlv.foldlM ((.mk ListProd3.nil l1 l2) : Prod3 (ListProd3 Nat Nat Level) _ _) (fun x y z (.mk R l1 l2) => do
          let .mk z l1 l2 ← mvarifyLTnodesIn z l1 l2
          return .mk (.cons x y z R) l1 l2)
        let md : BackStepMetadata :=
          match thm.name with
          | .inr x => .string s!"{repr x}"
          | .inl x => .std x.toString
        mtrace on .one with s!" calling addBackCandidate"
        let (x,y) ← addBackCandidate l1 l2 cfg st igc cand ta la target_goal_id thm embData .none md
        q1 (.mk y x l1 l2)
        ) q0
      ) <| fun (.mk cand igc l1 l2) => do
        mtrace on .one with s!"[addBackCandOfStd] adding candidates {← cand.foldlM ListProd4.nil (fun v x y z _ w => return .cons v (repr  x.thmData) y (repr z) w)}"
        let st := {st with id_gen_cand := igc, backCandScores := cand.append st.backCandScores}
        return .mk st l1 l2


#check mvarifyLTnodesIn
#check mvarifyTnodesRecWiContextIn

-- #exit


def addBackCandOfRW (l1 : LocalContext) (l2 : LocalInstances)
  (cfg : SearchConfig) (st : SearchState (List Nat))
  (target_goal_id : Nat) (target_goal_type : Expr)
  : MetaM (Prod3 (SearchState (List Nat)) LocalContext LocalInstances) :=
  do --trace set Tracing.Flags.none in do
  mtrace on .two with s!"[addBackCandOfRW] call embedBackRWMain' on {← PpExpr target_goal_type l1 l2}"
  match target_goal_type with
  | .forallE .. | .letE .. =>
    -- ↑↓ is an attempted optimization : ∀-goals will be introed and we don't want the same
    -- rws twice
    return .mk st l1 l2
  | _ =>
    mtrace on .two with s!"[addBackCandOfRW] call embedBackRWMain' on {← st.rwBackPaIn.ppS l1 l2 [] 0}"
    let .mk embs l1 l2 ← embedBackRWMain l1 l2
      st.thmData st.rwBackPaIn.getIndicesS cfg.revCountMax [] target_goal_type st.rwBackPaIn
    embs.foldlMcps (.mk (.nil : ListProd5 Nat BackCandData Nat ScoreType (List (CSetTrie (List Nat) Nat))) st.id_gen_cand l1 l2 : Prod4 _ _ _ _) (fun thmInd embDatas (.mk cand igc l1 l2) q0 => do
      let thm := st.thm_data[thmInd]!
      embDatas.foldlMcps (.mk cand igc l1 l2 : Prod4 _ _ _ _) (fun emb dirs extW (.mk cand igc l1 l2) q1 => do
        mtrace on .one with s!"[addBackCandOfRW] emb via ln {← emb.ln.foldlM ListProd.nil (fun y z w => return .cons y (← PpExpr z l1 l2) w)}"
        mtrace on .one with s!"[addBackCandOfRW] igc {igc}"
        mtrace on .one with s!"[addBackCandOfRW] looking at thm {repr thm.name}"
        let .mk ta l1 l2 ← emb.tn.foldlM ((.mk ListProd3.nil l1 l2) : Prod3 (ListProd3 Nat Nat Expr) _ _) (fun x y z (.mk R l1 l2) => do
          let .mk z l1 l2 ← mvarifyTnodesRecWiContextIn z l1 l2
          return .mk (.cons x y z R) l1 l2)
        mtrace on .one with s!"[addBackCandOfRW] ta {← ta.foldlM ListProd3.nil (fun x y z w => return .cons x y (← PpExpr z l1 l2) w)}"
        let .mk la l1 l2 ← emb.tlv.foldlM ((.mk ListProd3.nil l1 l2) : Prod3 (ListProd3 Nat Nat Level) _ _) (fun x y z (.mk R l1 l2) => do
          let .mk z l1 l2 ← mvarifyLTnodesIn z l1 l2
          return .mk (.cons x y z R) l1 l2)
        mtrace on .one with s!"[addBackCandOfRW] la {repr la}"
        mtrace on .one with s!"[addBackCandOfRW] igc {igc}"
        let md : BackStepMetadata :=
          match thm.name with
          | .inr x => .string s!"{repr x}"
          | .inl x => .std x.toString
        let (x,y) ← addBackCandidate l1 l2 cfg st igc cand ta la target_goal_id thm emb (.some dirs target_goal_type extW) md
        q1 (.mk y x l1 l2)) q0
      ) <| fun (.mk cand igc l1 l2) => do
        mtrace on .one with s!"[addBackCandOfRW] adding candidates {← cand.foldlM ListProd4.nil (fun v x y z _ w => return .cons v (repr  x.thmData) y (repr z) w)}"
        let st := {st with id_gen_cand := igc, backCandScores := cand.append st.backCandScores}
        return .mk st l1 l2



#print embedBackData

-- Select

-- pre integrate with
#check embedBackPreIntegrate
-- In ↓ follow docs suggestion
#check embedBackRWPreIntegrate

-- for inductions ↓
#check inductiveInductionData
#check functionalInductionData
-- In ↓, size of subgoal array correponds to tnodeRange
#check elimInductionData


-- ↓ + its docs suggestions
#check integrateBackwardStd

-- update ranks

-- query forw backwards applicable to new goals


#print BackCandData

def integrateBackwardFull (l1 : LocalContext) (l2 : LocalInstances) (cfg : SearchConfig) (st : SearchState (List Nat))
  (data : BackCandData)
  : MetaM (Prod3 (SearchState (List Nat)) LocalContext LocalInstances) :=
  --trace set Tracing.Flags.none in
  match data.rwdata with
  | .none => do
      mtrace on .one with s!"[integrateBackwardFull] embedBackPreIntegrate"
      let .mk term tnodeRange l1 l2 ← embedBackPreIntegrate l1 l2
        data.thmData st.id_gen_back data.arg_lvls data.todo_lvls data.arg_exprs data.todo_expr
      mtrace on .one with s!"[integrateBackwardFull] term {← PpExpr term l1 l2}"
      let .mk nIs nGs st l1 l2 ← integrateBackwardStd l1 l2
        cfg.revCountMax data.targetGoal term data.md  tnodeRange data.ta data.la st
      mtrace on .one with s!"[integrateBackwardFull] adding to cycleAddBack : {← nGs.foldlM ListProd.nil (fun x y z => return .cons x (← PpExpr y l1 l2) z)}"
      mtrace on .one with s!"[integrateBackwardFull] adding to cycleAddForw : {← nIs.foldlM ListProd.nil (fun x y z => return .cons x (← PpExpr y l1 l2) z)}"
      let st := {st with cycleAddForw := nIs.append st.cycleAddForw, cycleAddBack := nGs.append st.cycleAddBack}
      return .mk st l1 l2
  | .some dirs target_goal_type extW => do
      let ia := st.introTree.gatherUGidsToGoalId data.targetGoal []
      let iaf := fun n => ia.orderedContains n
      mtrace on .one with s!"[integrateBackwardFull] embedBackRWPreIntegrate"
      embedBackRWPreIntegrate
        iaf l1 l2 st.depsCache dirs st.id_gen_back target_goal_type extW data.thmData data.arg_lvls data.todo_lvls data.arg_exprs data.todo_expr
        (fun l1 l2 => do
          mtrace on .one with s!"[integrateBackwardFull] fail"
          let st := {st with id_gen_back := st.id_gen_back + 1} -- necessary
          return .mk st l1 l2
          )
        <| fun term tnodeRange l1 l2 => do
          mtrace on .one with s!"[integrateBackwardFull] term {← PpExpr term l1 l2}"
          let .mk nIs nGs st l1 l2 ← integrateBackwardStd l1 l2
            cfg.revCountMax data.targetGoal term data.md tnodeRange data.ta data.la st
          mtrace on .one with s!"[integrateBackwardFull] adding to cycleAddBack : {← nGs.foldlM ListProd.nil (fun x y z => return .cons x (← PpExpr y l1 l2) z)}"
          mtrace on .one with s!"[integrateBackwardFull] adding to cycleAddForw : {← nIs.foldlM ListProd.nil (fun x y z => return .cons x (← PpExpr y l1 l2) z)}"
          let st := {st with cycleAddForw := nIs.append st.cycleAddForw, cycleAddBack := nGs.append st.cycleAddBack}
          return .mk st l1 l2


#check IntroTree.gatherUGidsToGoalId
