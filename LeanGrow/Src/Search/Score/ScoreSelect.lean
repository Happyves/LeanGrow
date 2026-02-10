
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/
import LeanGrowBeta.Search.Types
import LeanGrowBeta.Search.Score.Regularisation

open Lean Meta

inductive SelectType where
| back (_ : BackCandData) | forw (_ : ForwCandData) | ind (_ : Prod3 TargetType Nat Expr) | none
deriving Inhabited

def SelectType.pp : SelectType → String
  | .back B => s!"back {repr B.thmData.name}"
  | .forw B => s!"forw {repr B.term.getAppFn}" -- flawed for rw ...
  | .ind B => s!"indu {repr B.1.pp}"
  | _ => "none"


def Array.sInsert
  (sofar : Array (Prod3 Float  SelectType Nat))
  (score : Float) (data : SelectType) (cand_id : Nat)
  : Array (Prod3 Float  SelectType Nat) :=
    let rec shift (i : Nat) (rep : (Prod3 Float  SelectType Nat)) (A : Array (Prod3 Float  SelectType Nat)) : Array (Prod3 Float  SelectType Nat) :=
      if _ : i < A.size
      then
        let nx := A[i]
        shift (i+1) nx (A.set! i rep)
      else
        A
    let rec main (i : Nat) (A : Array (Prod3 Float  SelectType Nat)) : Array (Prod3 Float  SelectType Nat) :=
      if _ : i < A.size
      then
        let cs := A[i].1
        if score > cs
        then
          shift i ⟨score, data, cand_id⟩ A
        else
          main (i+1) A
      else
        A
    main 0 sofar


#check 1


def ScoreType.avg : ScoreType → Float :=
  fun x => (x.back + x.forw + x.spe) / 3

def selectBatchOfBestScoresCommon
  (cfg : SearchConfig) (st : SearchState (List Nat))
  : Array (Prod3 Float  SelectType Nat) :=
  let init : Array (Prod3 Float  SelectType Nat) := Array.replicate cfg.addBatchSize ⟨0, .none, 0⟩
  let (sofar,lowest) := st.backCandScores.foldl (init,0) (fun ci data time absolutScore _ (sofar,lowest) =>
    let absolutScore := absolutScore.avg
    let hs := cfg.regulariser_bH absolutScore (getCandGoalHeight st.goalHeights data.targetGoal)
    let ds := cfg.regulariser_bD absolutScore (getCandBackDepth st.backDepths data.targetGoal)
    let spe := cfg.customRegulariser_back absolutScore time data st
    let score := (spe + hs + ds) / 3
    if score > lowest
    then
      let sofar := sofar.sInsert score (.back data) ci
      let lowest := sofar[sofar.size - 1]!.1
      (sofar,lowest)
    else
      (sofar,lowest)
    )
  let (sofar,lowest) := st.forwCandScores.foldl (sofar,lowest) (fun ci data time absolutScore _ _ (sofar,lowest) =>
    let absolutScore := absolutScore.avg
    let hs := cfg.regulariser_fH absolutScore (getCandForwHeight st.forwHeights data.UGinds)
    let ds := cfg.regulariser_fD absolutScore (getCandForwDepth st.forwDepths data.UGinds)
    let spe := cfg.customRegulariser_forw absolutScore time data st
    let score := (spe + hs + ds) / 3
    if score > lowest
    then
      let sofar := sofar.sInsert score (.forw data) ci
      let lowest := sofar[sofar.size - 1]!.1
      (sofar,lowest)
    else
      (sofar,lowest)
    )
  let (sofar,_) := st.inductCandScores.foldl (sofar,lowest) (fun ci time tar target goalE absolutScore (sofar,lowest) =>
    let hs := cfg.regulariser_bH absolutScore (getCandGoalHeight st.goalHeights target)
    let ds := cfg.regulariser_bD absolutScore (getCandBackDepth st.backDepths target)
    let spe := cfg.customRegulariser_indu absolutScore time tar st
    let score := (spe + hs + ds) / 3
    if score > lowest
    then
      let sofar := sofar.sInsert score (.ind ⟨tar, target,goalE⟩) ci
      let lowest := sofar[sofar.size - 1]!.1
      (sofar,lowest)
    else
      (sofar,lowest)
    )
  sofar


def selectBatchOfBestScoresSplit
  (cfg : SearchConfig) (st : SearchState (List Nat))
  : Array (Prod3 Float  SelectType Nat) :=
  let init : Array (Prod3 Float  SelectType Nat) := Array.replicate cfg.backBatchSize ⟨0, .none, 0⟩
  let (sofarB,_) := st.backCandScores.foldl (init,0) (fun ci data time absolutScore _ (sofar,lowest) =>
    let absolutScore := absolutScore.avg
    let hs := cfg.regulariser_bH absolutScore (getCandGoalHeight st.goalHeights data.targetGoal)
    let ds := cfg.regulariser_bD absolutScore (getCandBackDepth st.backDepths data.targetGoal)
    let spe := cfg.customRegulariser_back absolutScore time data st
    let score := (spe + hs + ds) / 3
    if score > lowest
    then
      let sofar := sofar.sInsert score (.back data) ci
      let lowest := sofar[sofar.size - 1]!.1
      (sofar,lowest)
    else
      (sofar,lowest)
    )
  let init : Array (Prod3 Float  SelectType Nat) := Array.replicate cfg.forwBatchSize ⟨0, .none, 0⟩
  let (sofarF,_) := st.forwCandScores.foldl (init,0) (fun ci data time absolutScore _ _ (sofar,lowest) =>
    let absolutScore := absolutScore.avg
    let hs := cfg.regulariser_fH absolutScore (getCandForwHeight st.forwHeights data.UGinds)
    let ds := cfg.regulariser_fD absolutScore (getCandForwDepth st.forwDepths data.UGinds)
    let spe := cfg.customRegulariser_forw absolutScore time data st
    let score := (spe + hs + ds) / 3
    if score > lowest
    then
      let sofar := sofar.sInsert score (.forw data) ci
      let lowest := sofar[sofar.size - 1]!.1
      (sofar,lowest)
    else
      (sofar,lowest)
    )
  let init : Array (Prod3 Float  SelectType Nat) := Array.replicate cfg.induBatchSize ⟨0, .none, 0⟩
  let (sofarI,_) := st.inductCandScores.foldl (init,0) (fun ci time tar target goalE absolutScore (sofar,lowest) =>
    let hs := cfg.regulariser_bH absolutScore (getCandGoalHeight st.goalHeights target)
    let ds := cfg.regulariser_bD absolutScore (getCandBackDepth st.backDepths target)
    let spe := cfg.customRegulariser_indu absolutScore time tar st
    let score := (spe + hs + ds) / 3
    if score > lowest
    then
      let sofar := sofar.sInsert score (.ind ⟨tar, target,goalE⟩) ci
      let lowest := sofar[sofar.size - 1]!.1
      (sofar,lowest)
    else
      (sofar,lowest)
    )
  (sofarB ++ sofarF ++ sofarI)

def selectBatchOfBestScores
  (cfg : SearchConfig) (st : SearchState (List Nat))
  : Array (Prod3 Float  SelectType Nat) :=
  if cfg.splitBatches
  then
    selectBatchOfBestScoresSplit cfg st
  else
    selectBatchOfBestScoresCommon cfg st


def removeCand (st : SearchState (List Nat)) (rawCandInds : List Nat) : SearchState (List Nat) :=
  let inds := rawCandInds.mergeSort
  let nb := st.backCandScores.foldl ListProd5.nil (fun id a b c d e =>
    if inds.orderedContains id then e else .cons id a b c d e)
  let nf := st.forwCandScores.foldl ListProd6.nil (fun id a b c d e f =>
    if inds.orderedContains id then f else .cons id a b c d e f)
  let ni := st.inductCandScores.foldl ListProd6.nil (fun id x a b c d e =>
    if inds.orderedContains id then e else .cons id x a b c d e)
  {st with backCandScores := nb, forwCandScores := nf, inductCandScores := ni}




-- # Custom regularisers

def regBackBreadth
  (maxTime : Nat)
  (score : Float) (time : Nat) (data : BackCandData) (st : SearchState (List Nat)) : Float :=
  let timeFac := 1 - ((maxTime.toFloat - time.toFloat) / maxTime.toFloat)
  let idFac := 1 - ((st.id_gen_goal.toFloat - data.targetGoal.toFloat) / st.id_gen_goal.toFloat)
  timeFac * idFac * score

def regBackDepth
  (maxTime : Nat)
  (score : Float) (time : Nat) (data : BackCandData) (st : SearchState (List Nat)) : Float :=
  let timeFac := ((maxTime.toFloat - time.toFloat) / maxTime.toFloat)
  let idFac := ((st.id_gen_goal.toFloat - data.targetGoal.toFloat) / st.id_gen_goal.toFloat)
  timeFac * idFac * score
