
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrowBeta.Search.API.ScoreCore

open Lean Meta

#check 1

#check IntroTree.forwGoalCoherent?

def forwGoalCoherentS (target_forw_ids : List Nat) (goalI : Nat) (IT : IntroTree (List Nat)) :=
  @IntroTree.forwGoalCoherent? (List Nat) _ id target_forw_ids goalI IT


#check 1

@[inline]
def updateScoreWithNewGoal (l1 : LocalContext) (l2 : LocalInstances)
  (revCountMax  : Nat) (cycleAddBack : ListProd Nat Expr)
  (target_forw_ids : List Nat) (T : CPaIn (List Nat)) (IT : IntroTree (List Nat))
  (oldScore : ScoreType)
  : MetaM (Prod4 ScoreType Bool LocalContext LocalInstances) :=
  do-- do --trace set Tracing.Flags.none in do
  for data in T.loadData do
      for j in [:data.lvlNum] do
        let _ ← mkLevelMVarOfName (lnode data.sampleName j 0)
      let mut i := 0
      for T in data.types do
        let _ ← mkMvarStdWiCoI (lnode data.sampleName i 0) T l1 l2
        i := i+1
  cycleAddBack.foldlMcps (.mk oldScore false l1 l2 : Prod4 _ _ _ _) (fun new_goal_id new_goal_type (.mk score up? l1 l2) q => do
    let relevant := forwGoalCoherentS target_forw_ids new_goal_id IT
    if relevant
    then
      let inds := T.pi.getIndicesS
      let .mk here? l1 l2 ← genQueryBackMainS l1 l2 inds revCountMax new_goal_type T.pi T.weights
      match here? with
        | .none => q (.mk score up? l1 l2)
        | .some here =>
            mtrace on .one with s!"[scoreWithGoals] here {here}"
            q (.mk {score with back := (here / T.totalWeight) + score.back} true l1 l2)
            -- remember that oldscore is alread noramlised
    else
      q (.mk score up? l1 l2))
      <| fun x => return x



#check 1


def genQueryForwNoLoadMainS :=
  @PaIn.genQueryForwNoLoadMain (List Nat) _
    (List.orderedIntersect) (List.orderedDiff) List.isEmpty


#check 1

@[inline]
partial def updateForwScoreWithNewForw
  (l1 : LocalContext) (l2 : LocalInstances) (cycleAddForw : ListProd Nat Expr)
  (targets : List Nat) (sts : CSetTrie (List Nat) Nat) (IT : IntroTree (List Nat))
  (oldScore : ScoreType)
  -- {β : Type}  (q : Option ScoreType → List (CSetTrie (List Nat) Nat) → MetaM β) : MetaM β :=
  : MetaM (Prod (Option ScoreType) (List (CSetTrie (List Nat) Nat))) :=
  let rec relevant : ListProd Nat Expr → Bool
    | .nil => false
    | .cons new_forw_id _ more => if forwCoherentS targets new_forw_id IT then true else relevant more
  do --trace set Tracing.Flags.none in do
  if !(relevant cycleAddForw)
  then
    mtrace on .one with s!"[updateForwScoreWithNewForw] forward additions {targets} irrelevant, skipping"
    return .mk .none .nil
  else
    let Q ← mergeLtxForForwIdsS targets IT .dead
    mtrace on .one with s!"[updateForwScoreWithNewForw] relevant ltx : {← Q.ppS l1 l2 [] 0}"
    let .mk progress? here? pointas ← genQueryForwWiLoadMainS l1 l2
      sts.loadData sts.weights sts.samHypDict Q sts.settrie
    if here? == .none && progress?
    then
      mtrace on .one with s!"[updateForwScoreWithNewForw] made no progress"
      return .mk .none .nil
    else
      let score := match here? with | .none => 0 | .some s => s / sts.totalWeight
      mtrace on .one with s!"[updateForwScoreWithNewForw] noremalised new forward score {score}"
      let pointas : List (CSetTrie (List Nat) Nat) := pointas.foldl (fun R s => ⟨s, sts.loadData, sts.weights, sts.totalWeight, sts.samHypDict⟩ :: R ) []
      return .mk (.some ({oldScore with forw := score + oldScore.forw})) pointas


#check forwCoherentS
#check backCoherent
#check mergeLtxForGoalIdS
#check mergeLtxForForwIdsS
#check genQueryForwWiLoadMainS

-- #exit

@[inline]
partial def updateGoalScoreWithNewForw
  (l1 : LocalContext) (l2 : LocalInstances) (cycleAddForw : ListProd Nat Expr)
  (target : Nat) (sts : CSetTrie (List Nat) Nat) (IT : IntroTree (List Nat))
  (oldScore : ScoreType)
  -- {β : Type}  (q : Option ScoreType → List (CSetTrie (List Nat) Nat) → MetaM β) : MetaM β :=
  : MetaM (Prod (Option ScoreType) (List (CSetTrie (List Nat) Nat))) :=
  let rec relevant : ListProd Nat Expr → Bool
    | .nil => false
    | .cons new_forw_id _ more => if backCoherent target new_forw_id IT then true else relevant more
  do --trace set Tracing.Flags.none in do
  if !(relevant cycleAddForw)
  then
    mtrace on .one with s!"[updateGoalScoreWithNewForw] forward additions {target} irrelevant, skipping"
    return .mk .none .nil
  else
    let Q ← mergeLtxForGoalIdS target IT
    mtrace on .one with s!"[updateGoalScoreWithNewForw] relevant ltx : {← Q.ppS l1 l2 [] 0}"
    let .mk progress? here? pointas ← genQueryForwWiLoadMainS l1 l2
      sts.loadData sts.weights sts.samHypDict Q sts.settrie
    if here? == .none && progress?
    then
      mtrace on .one with s!"[updateGoalScoreWithNewForw] made no progress"
      return .mk .none .nil
    else
      let score := match here? with | .none => 0 | .some s => s / sts.totalWeight
      mtrace on .one with s!"[updateGoalScoreWithNewForw] noremalised new forward score {score}"
      let pointas : List (CSetTrie (List Nat) Nat) := pointas.foldl (fun R s => ⟨s, sts.loadData, sts.weights, sts.totalWeight, sts.samHypDict⟩ :: R ) []
      return .mk (.some ({oldScore with forw := score + oldScore.forw})) pointas


#check 1

-- #exit

@[inline]
def updateScores
  (l1 : LocalContext) (l2 : LocalInstances)
  (cfg : SearchConfig) (st : SearchState (List Nat))
  : MetaM (Prod3 (SearchState (List Nat)) LocalContext LocalInstances) := do
  -- trace set Tracing.Flags.none in
  let .mk nf l1 l2 ← st.forwCandScores.foldlM (.mk (.nil : ListProd6 Nat ForwCandData Nat ScoreType (CPaIn (List Nat)) (List (CSetTrie (List Nat) Nat))) l1 l2 : Prod3 _ _ _)
    (fun id data time score B F (.mk res l1 l2) => do
        mtrace on .one with s!"[updateScores]  updating forward candidate {id} with score {repr score} and timer {time}"
        let .mk score up1? l1 l2 ← updateScoreWithNewGoal l1 l2 cfg.revCountMax st.cycleAddBack data.UGinds B st.introTree score
            -- *note* grocely inefficient ; for example `updateGoalScoreWithNewForw.relevant` will be recomputed for subtrees from a same  forward candidate
        let .mk score pointas up2? ← F.foldlM (fun (.mk score pts u?) f => do
          let .mk here? npts ← updateForwScoreWithNewForw l1 l2 st.cycleAddForw data.UGinds f st.introTree score
          match here? with
          | .none => return (.mk score (f :: pts) u?)
          | .some here =>  return .mk here (npts ++ pts) true
          ) (.mk score ([] : List (CSetTrie (List Nat) Nat)) false : Prod3 ..)
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
  let .mk nb l1 l2 ← st.backCandScores.foldlM (.mk (.nil : ListProd5 Nat BackCandData Nat ScoreType (List (CSetTrie (List Nat) Nat))) l1 l2 : Prod3 _ _ _)
    (fun id data time score F (.mk res l1 l2) => do
      mtrace on .one with s!"[updateScores]  updating backward candidate {id} with score {repr score} and timer {time}"
      let .mk score pointas up2? ← F.foldlM (fun (.mk score pts u?) f => do
        let (here?, npts) ← updateGoalScoreWithNewForw l1 l2 st.cycleAddForw data.targetGoal f st.introTree score
        match here? with
        | .none => return (.mk score (f :: pts) u?)
        | .some here =>  return (.mk here (npts ++ pts) true)
            ) (.mk score [] false : Prod3 ..)
      if up2?
      then
        mtrace on .one with s!"[updateScores] new score {repr score}"
        return (.mk (.cons id data cfg.default_relevance_timer score pointas res) l1 l2)
      else
        if time == 0
        then
          mtrace on .one with s!"[updateScores] dropped"
          return (.mk res l1 l2)
        else
          mtrace on .one with s!"[updateScores] decreased timer"
          return (.mk (.cons id data (time - 1) score F res) l1 l2)
      )
  let st := {st with backCandScores := nb}
  return .mk st l1 l2
