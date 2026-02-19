
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Search.API.ScoreCore

open Lean Meta

#check 1

#check IntroTree.forwGoalCoherent?

-- #exit

def forwGoalCoherentS :=
  IntroTree.forwGoalCoherent?
    UInt32Array.isEmpty (fun x y => y.oContains x.toUInt32) UInt32Array.diff


#check 1

@[inline]
def updateScoreWithNewGoal (l1 : LocalContext) (l2 : LocalInstances)
  (revCountMax  : Nat) (cycleAddBack : ListProd Nat Expr)
  (target_forw_ids : UInt32Array) (T : thmGenDataEntry UInt32Array) (IT : IntroTree UInt32Array)
  (oldScore : ScoreType)
  : MetaM (Prod4 ScoreType Bool LocalContext LocalInstances) :=
  do
  mtracing
  cycleAddBack.foldlMcps (.mk oldScore false l1 l2 : Prod4 _ _ _ _) (fun new_goal_id new_goal_type (.mk score up? l1 l2) q => do
    let relevant := forwGoalCoherentS target_forw_ids new_goal_id IT
    if relevant
    then
      let inds := T.goalPain.getIndicesS
      let .mk here l1 l2 ← PaIn.genQueryBackNoLoadMain_S l1 l2 inds revCountMax new_goal_type T.goalPain
      let new := here.foldl 0 (fun i s => T.goalWeights[i.toNat]! + s)
      mtrace on .one with s!"[scoreWithGoals] here {here}"
      q (.mk {score with back := (new.toFloat / T.goalTotal.toFloat) + score.back} (if here.isEmpty then up? else true) l1 l2)
      -- remember that oldscore is alread noramlised
    else
      q (.mk score up? l1 l2))
      <| fun x => return x



#check 1

-- #exit

@[inline]
partial def updateForwScoreWithNewForw
  (l1 : LocalContext) (l2 : LocalInstances) (cycleAddForw : ListProd3 Nat FVarId Expr)
  (targets : UInt32Array) (scoredata : thmGenDataEntry UInt32Array) (sts : SetTrieP (Nat × Nat) UInt32Array PaIn)
  (IT : IntroTree UInt32Array)
  (oldScore : ScoreType)
  : MetaM (Prod (Option ScoreType) (List (SetTrieP (Nat × Nat) UInt32Array PaIn))) :=
  let rec relevant : ListProd3 Nat FVarId Expr → Bool
    | .nil => false
    | .cons new_forw_id _ _ more => if forwCoherentS targets new_forw_id IT then true else relevant more
  do
  mtracing
  if !(relevant cycleAddForw)
  then
    mtrace on .one with s!"[updateForwScoreWithNewForw] forward additions {targets} irrelevant, skipping"
    return .mk .none .nil
  else
    let Q ← mergeLtxForForwIdsS targets IT .dead
    mtrace on .one with s!"[updateForwScoreWithNewForw] relevant ltx : {← Q.ppS l1 l2 [] 0}"
    let .mk progress? here? pointas ← genQueryForwNoLoadMainS l1 l2 Q sts
    if here?.isEmpty && ! progress?
    then
      mtrace on .one with s!"[updateForwScoreWithNewForw] made no progress"
      return .mk .none .nil
    else
      let fscore := here?.foldl (fun r (_,s) => r+s) 0
      let fscore := fscore.toFloat / scoredata.hypTotal.toFloat
      mtrace on .one with s!"[updateForwScoreWithNewForw] noremalised new forward score {fscore}"
      return .mk (.some ({oldScore with forw := fscore + oldScore.forw})) pointas


#check forwCoherentS
#check backCoherent
#check mergeLtxForGoalIdS
#check mergeLtxForForwIdsS

--#exit

@[inline]
partial def updateGoalScoreWithNewForw
  (l1 : LocalContext) (l2 : LocalInstances) (cycleAddForw : ListProd3 Nat FVarId Expr)
  (target : Nat) (scoredata : thmGenDataEntry UInt32Array) (sts : SetTrieP (Nat × Nat) UInt32Array PaIn)
  (IT : IntroTree UInt32Array)
  (oldScore : ScoreType)
  : MetaM (Prod (Option ScoreType) (List (SetTrieP (Nat × Nat) UInt32Array PaIn))) :=
  let rec relevant : ListProd3 Nat FVarId Expr → Bool
    | .nil => false
    | .cons new_forw_id _ _ more => if backCoherent target new_forw_id IT then true else relevant more
  do
  mtracing
  if !(relevant cycleAddForw)
  then
    mtrace on .one with s!"[updateGoalScoreWithNewForw] forward additions {target} irrelevant, skipping"
    return .mk .none .nil
  else
    let Q ← mergeLtxForGoalIdS target IT
    mtrace on .one with s!"[updateGoalScoreWithNewForw] relevant ltx : {← Q.ppS l1 l2 [] 0}"
    let .mk progress? here? pointas ← genQueryForwNoLoadMainS l1 l2 Q sts
    if here?.isEmpty && ! progress?
    then
      mtrace on .one with s!"[updateGoalScoreWithNewForw] made no progress"
      return .mk .none .nil
    else
      let fscore := here?.foldl (fun r (_,s) => r+s) 0
      let fscore := fscore.toFloat / scoredata.hypTotal.toFloat
      mtrace on .one with s!"[updateForwScoreWithNewForw] noremalised new forward score {fscore}"
      return .mk (.some ({oldScore with forw := fscore + oldScore.forw})) pointas


#check 1

-- #exit

@[inline]
def updateScores
  (l1 : LocalContext) (l2 : LocalInstances)
  (cfg : SearchConfig UInt32Array) (st : SearchState UInt32Array)
  : MetaM (Prod3 (SearchState UInt32Array) LocalContext LocalInstances) :=
  do
  mtracing
  let .mk nf l1 l2 ← st.forwCandScores.foldlM (.mk (.nil : ListProd6 Nat ForwCandData Nat ScoreType (thmGenDataEntry UInt32Array) (List (SetTrieP (Nat × Nat) UInt32Array PaIn))) l1 l2 : Prod3 _ _ _)
    (fun id data time score B F (.mk res l1 l2) => do
        mtrace on .one with s!"[updateScores]  updating forward candidate {id} with score {repr score} and timer {time}"
        let .mk score up1? l1 l2 ← updateScoreWithNewGoal l1 l2 cfg.revCountMax st.cycleAddBack data.UGinds B st.introTree score
            -- *note* grocely inefficient ; for example `updateGoalScoreWithNewForw.relevant` will be recomputed for subtrees from a same  forward candidate
        let .mk score pointas up2? ← F.foldlM (fun (.mk score pts u?) f => do
          let .mk here? npts ← updateForwScoreWithNewForw l1 l2 st.cycleAddForw data.UGinds B f st.introTree score
          match here? with
          | .none => return (.mk score (f :: pts) u?)
          | .some here =>  return .mk here (npts ++ pts) true
          ) (.mk score ([] : List (SetTrieP (Nat × Nat) UInt32Array PaIn)) false : Prod3 ..)
        if up1? || up2?
        then
          mtrace on .one with s!"[updateScores] new score {repr score}"
          return (.mk (.cons id data cfg.default_relevance_timer score B pointas res) l1 l2)
        else
          if time == 0
          then
            mtrace on .one with s!"[updateScores] dropped"
            return (.mk res l1 l2)
          else
            mtrace on .one with s!"[updateScores] decreased timer"
            return (.mk (.cons id data (time - 1) score B F res) l1 l2)
      )
  let st := {st with forwCandScores := nf}
  let .mk nb l1 l2 ← st.backCandScores.foldlM (.mk (.nil : ListProd6 Nat BackCandData Nat ScoreType (thmGenDataEntry UInt32Array) (List (SetTrieP (Nat × Nat) UInt32Array PaIn))) l1 l2 : Prod3 _ _ _)
    (fun id data time score B F (.mk res l1 l2) => do
      mtrace on .one with s!"[updateScores]  updating backward candidate {id} with score {repr score} and timer {time}"
      let .mk score pointas up2? ← F.foldlM (fun (.mk score pts u?) f => do
        let (here?, npts) ← updateGoalScoreWithNewForw l1 l2 st.cycleAddForw data.targetGoal B f st.introTree score
        match here? with
        | .none => return (.mk score (f :: pts) u?)
        | .some here =>  return (.mk here (npts ++ pts) true)
            ) (.mk score [] false : Prod3 ..)
      if up2?
      then
        mtrace on .one with s!"[updateScores] new score {repr score}"
        return (.mk (.cons id data cfg.default_relevance_timer score B pointas res) l1 l2)
      else
        if time == 0
        then
          mtrace on .one with s!"[updateScores] dropped"
          return (.mk res l1 l2)
        else
          mtrace on .one with s!"[updateScores] decreased timer"
          return (.mk (.cons id data (time - 1) score B F res) l1 l2)
      )
  let st := {st with backCandScores := nb}
  return .mk st l1 l2
