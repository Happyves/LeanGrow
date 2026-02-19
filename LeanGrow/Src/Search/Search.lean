
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Search.Forward
import LeanGrow.Src.Search.Backward
import LeanGrow.Src.Search.Induction
import LeanGrow.Src.Search.API.Assembly
import LeanGrow.Src.Search.Score.ScoreSelect
import LeanGrow.Src.Search.API.ScoreUpdate
-- import LeanGrow.Src.Search.TacticSupport.SupportMain -- not ported yet


open Lean Meta


def SearchState.pp (l1 : LocalContext) (l2 : LocalInstances)
  (st : SearchState (List Nat)) : MetaM String := do
  withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
  let mut msg := "[searchCore] state:\n\n"
  msg := msg ++ s!"[searchCore] back-tree :\n{← st.backTree.pp 0}\n\n"
  msg := msg ++ s!"[searchCore] intro-tree :\n{st.introTree.ppDirs 0}\n\n"
  msg := msg ++ "[searchCore] forward decls:\n"
  for ug in [:st.id_gen_forw] do
    let node := if st.uNodes.binSearchContains ug (· < ·) then unode ug else gnode ug
    let T ← (⟨node⟩ : FVarId).getType
    msg := msg ++ s!"{ug} : {← ppExpr T}\n"
  return msg

#check BackTree.ppDirs

-- #exit

@[inline]
def runTacticSupportOrNot (cfg : SearchConfig)  (st : SearchState (List Nat))
  {α : Sort _} (k : SearchState (List Nat) → MetaM α) : MetaM α :=
  if cfg.tacticSupport
  then k st --runTacticSupport cfg st k -- reactivate after port
  else k st

def SearchState.printBackCand (l1 : LocalContext) (l2 : LocalInstances) (st : SearchState (List Nat)) : MetaM String := do
  withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
  st.backCandScores.foldlM "[printBackCand]\n" (fun candid data time score _ msg => do
    return msg ++ s!"candid {candid}, thm {repr data.thmData} on goal {data.targetGoal} with time {time} and score {repr score}\n")

def SearchState.printForwCand (l1 : LocalContext) (l2 : LocalInstances) (st : SearchState (List Nat)) : MetaM String := do
  withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
  st.forwCandScores.foldlM "[printForwCand]\n" (fun candid data time score _ _ msg => do
    return msg ++ s!"candid {candid}, term of type {← ppExpr data.type} with ugIs {data.UGinds} with time {time} and score {repr score}\n")

def SearchState.printInduCand (l1 : LocalContext) (l2 : LocalInstances) (st : SearchState (List Nat)) : MetaM String := do
  withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
  st.inductCandScores.foldlM "[printInduCand]\n" (fun candid time data targetI targetE score msg => do
    return msg ++ s!"candid {candid}, thm {repr data.pp} on goal {targetI} of type {← ppExpr targetE} with time {time} and score {repr score}\n")

#check BackTree.assembleMain
#check updateScores
#check Array.mapIdx



partial def searchCore (l1 : LocalContext) (l2 : LocalInstances)
  (cfg : SearchConfig)  (st : SearchState (List Nat)) (fuel : Nat)
  : MetaM (Prod4 (SearchState (List Nat)) (ListProd Expr (List Nat)) LocalContext LocalInstances) :=
  do -- trace set Tracing.Flags.all in do
  mtrace on .zero with (← st.pp l1 l2)
  mtrace on .two with s!"[searchCore] back tree with dirs : {st.backTree.ppDirs 0}"
  mtrace on .zero with s!"[searchCore] fuel : {fuel}"
  mtrace on .three with s!"[searchCore] forwHeights : {st.forwHeights.mapIdx (fun i s => (i,s))}"
  mtrace on .three with s!"[searchCore] goalHeights : {st.goalHeights.mapIdx (fun i s => (i,s))}"
  mtrace on .three with s!"[searchCore] forwDepths : {st.forwDepths.mapIdx (fun i s => (i,s.depth))}"
  mtrace on .three with s!"[searchCore] backDepths : {st.backDepths.mapIdx (fun i s => (i,s.depth))}"
  mtrace on .three with s!"[searchCore] depsCache : {st.depsCache.mapIdx (fun i s => (i,s.map (FVarId.name <| LocalDecl.fvarId · )))}"
  if fuel == 0
  then return .mk st .nil l1 l2
  else
    runTacticSupportOrNot cfg st <| fun st => do
      let cAF := st.cycleAddForw
      mtrace on .one with s!"[searchCore] cAF : {← cAF.foldlM ListProd.nil (fun x y z => return .cons x (← PpExpr y l1 l2) z)}"
      let .mk st l1 l2 ← cAF.foldlM (.mk st l1 l2 : Prod3 _ _ _) (fun fid fT (.mk st l1 l2) => do
        let .mk st l1 l2 ← addForwCandOfRW l1 l2  cfg st fid fT
        --let .mk st l1 l2 ← addBackCandOfInductForw l1 l2 cfg st fid
        return (.mk st l1 l2))
      mtrace on .zero with s!"[searchCore] added cadidates from forward cycle additions"
      let cBF := st.cycleAddBack
      mtrace on .one with s!"[searchCore] cBF : {← cBF.foldlM ListProd.nil (fun x y z => return .cons x (← PpExpr y l1 l2) z)}"
      let .mk st l1 l2 ← cBF.foldlM (.mk st l1 l2 : Prod3 _ _ _) (fun fid fT (.mk st l1 l2) => do
        mtrace on .two with s!"[searchCore] looking at cycle addition {← PpExpr fT l1 l2}"
        mtrace on .two with s!"[searchCore] id_gen_cand {st.id_gen_cand}"
        let .mk st l1 l2 ← addBackCandOfRW l1 l2 cfg st fid fT
        mtrace on .two with s!"[searchCore] id_gen_cand {st.id_gen_cand}"
        let .mk st l1 l2 ← addBackCandOfStd l1 l2 cfg st fid fT
        mtrace on .two with s!"[searchCore] id_gen_cand {st.id_gen_cand}"
        let .mk st l1 l2 ← addBackCandOfInductGoal l1 l2 cfg st fid fT
        return (.mk st l1 l2))
      mtrace on .zero with s!"[searchCore] added cadidates from backward cycle additions"
      mtrace on .one with s!"[searchCore] back candidates\n{← st.printBackCand l1 l2}"
      mtrace on .one with s!"[searchCore] forw candidates\n{← st.printForwCand l1 l2}"
      mtrace on .one with s!"[searchCore] induct candidates\n{← st.printInduCand l1 l2}"
      let st := {st with cycleAddBack := .nil, cycleAddForw := .nil}
      mtrace on .zero with s!"[searchCore] flushed cycle additions"
      let .mk st l1 l2 ← addForwCandOfStdStep l1 l2 cfg st
      mtrace on .zero with s!"[searchCore] possibly added cadidates from standard forward step"
      mtrace on .one with s!"[searchCore] forw candidates\n{← st.printForwCand l1 l2}"
      let bestBatch := selectBatchOfBestScores cfg st
      mtrace on .zero with s!"[searchCore] best batch {repr <| bestBatch.map (fun ⟨x,y,z⟩ => (⟨x,y.pp,z⟩ : Prod3 _ _ _))} "
      let st := removeCand st (bestBatch.foldl (fun R x => x.3 :: R) [])
      mtrace on .zero with s!"[searchCore] remove best batch from candidates"
      mtrace on .three with s!"[searchCore] goalSpawn {repr st.goalSpawn}"
      let .mk st l1 l2 ← bestBatch.toList.foldlM (fun (.mk st l1 l2) x => do
        match x.2 with
        | .back b =>
            mtrace on .three with s!"[searchCore] integrate back with thm {repr b.thmData.name} and target {b.targetGoal}"
            mtrace on .three with s!"[searchCore] and arg_exprs {← b.arg_exprs.mapM (PpExpr · l1 l2)} "
            mtrace on .three with s!"[searchCore] id_gen_goal {st.id_gen_goal}"
            integrateBackwardFull l1 l2 cfg st b
            -- q st
        | .forw f =>
            mtrace on .three with s!"[searchCore] integrate forw with type {← PpExpr f.type l1 l2} and ugis {f.UGinds}"
            integrateForwardFull l1 l2 cfg st f
            -- q st
        | .ind i =>
            mtrace on .three with s!"[searchCore] integrate indu with tar {i.1.pp} target {i.2} of type {← PpExpr i.3 l1 l2}"
            integrateInduction l1 l2 cfg st i.1 i.2 i.3
            -- return .mk st l1 l2
        | .none => return (.mk st l1 l2) -- don't throw error as it may be that bestBatch overestimated the number of existing candidates
        ) (.mk st l1 l2 : Prod3 _ _ _)
      mtrace on .zero with s!"[searchCore] integrated best batch"
      let r@(.mk st sols l1 l2) ←BackTree.assembleMain l1 l2
        cfg.revCountMax st
      match sols with
      | .cons .. => return r
      | .nil =>
          mtrace on .zero with s!"[searchCore] assembled"
          let .mk st l1 l2 ← updateScores l1 l2 cfg st
          mtrace on .zero with s!"[searchCore] updated forward and backward candidates"
          let nics := st.inductCandScores.foldl .nil (fun ci time tar get ty sco R =>
            if time == 0 then R else .cons ci (time - 1) tar get ty sco R)
          let st := {st with inductCandScores := nics}
          mtrace on .zero with s!"[searchCore] updated induction candidates"
          searchCore l1 l2 cfg st (fuel - 1)


#check updateScores
#check PaIn.insertS
#check Array.mapIdx
#check FVarId.name
