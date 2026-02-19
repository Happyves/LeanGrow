
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Search.API.IntegrateForw
import LeanGrow.Src.Search.API.IntegrateBack
import LeanGrow.Src.Search.IntroTree.Operations
import LeanGrow.Src.Search.BackTree.Operations
import LeanGrow.Src.SampleGenScore.Gen.GenQueryForw
import LeanGrow.Src.SampleGenScore.Gen.GenQueryBack
import LeanGrow.Src.Core.Embedding.EmbedProcessBack


open Lean Meta


#check IntroTree.mergeGoalsForForwIds
#check IntroTree.mergeLtxForForwIds
#check PaIn.genQueryForwWiLoadMain
#check PaIn.genQueryBackNoLoadMain_S
#check PaIn.genQueryBackWiLoadMain
#check IntroTree.forwCoherent?

-- #exit

def mergeGoalsForForwIdsS :=
  IntroTree.mergeGoalsForForwIds
    UInt32Array.isEmpty UInt32Array.union UInt32Array.diff UInt32Array.empty

#check 1

def mergeLtxForForwIdsS :=
  @IntroTree.mergeLtxForForwIds _ MetaM _ _
    UInt32Array.isEmpty UInt32Array.union UInt32Array.diff UInt32Array.empty


#check 1

def genQueryForwNoLoadMainS :=
  PaIn.genQueryForwNoLoadMainLG
    UInt32Array.inter UInt32Array.diff UInt32Array.union UInt32Array.isEmpty
    UInt32Array.empty UInt32Array.subsetOf

#check 1

def genQueryBackWiLoadMainS  :=
  PaIn.genQueryBackWiLoadMain
    UInt32Array.isEmpty UInt32Array.inter UInt32Array.union UInt32Array.empty


#check 1

def forwCoherentS :=
  IntroTree.forwCoherent?
    UInt32Array.isEmpty (fun x y => y.oContains x.toUInt32) UInt32Array.diff

#check 1

-- #exit

/--
previously used to load types and level mvars, but we now expect that to be
already done when we load the `scoreThmKey`
-/
partial def scoreWithGoals (l1 : LocalContext) (l2 : LocalInstances)
  (revCountMax : Nat) (target_forw_ids : UInt32Array) (T : thmGenDataEntry UInt32Array) (IT : IntroTree UInt32Array)
  : MetaM (Prod3 Float LocalContext LocalInstances) :=
  do
  mtracing
  let rec @[specialize] inner (target_forw_ids : UInt32Array) :
    ListProd3 UInt32Array UInt32Array (IntroTree UInt32Array) → (Option (IntroTree UInt32Array))
    | .nil => (.none)
    | .cons _ foIds t more =>
        let I := foIds
        if (UInt32Array.diff target_forw_ids I).isEmpty
        then
          (.some t)
        else
          inner target_forw_ids more
  let rec @[specialize] locate (target_forw_ids : UInt32Array) : IntroTree UInt32Array → IntroTree UInt32Array
    | x@(.leaf ..) => x
    | x@(.node _ _ foIds _ _ kidsWdirs) =>
        let nx := (UInt32Array.diff target_forw_ids foIds)
        if nx.isEmpty
        then x
        else
          match inner nx kidsWdirs with
          | .none => panic s!"[mergeGoalsForForwIds] target {target_forw_ids} not found among directions"
          | .some T => locate nx T
  do
  mtrace on .one with s!"[scoreWithGoals] locating subtree for {target_forw_ids}, whithin {IT.pp 0}"
  let subIT := locate target_forw_ids IT
  mtrace on .one with s!"[scoreWithGoals] found {subIT.pp 0}"
  let inds := T.goalPain.getIndicesS
  let rec go (l1 : LocalContext) (l2 : LocalInstances) (it : List (IntroTree UInt32Array)) (score : Nat) : MetaM (Prod3 Nat LocalContext LocalInstances) := do
    match it with
    | [] => return .mk score l1 l2
    | .leaf _ _ _ gs _ :: more => do
      let Gs ← gs.buildAllS l1 l2 [] 0
      mtrace on .one with s!"[scoreWithGoals] built goals {← Gs.foldlM ListProd.nil (fun x y z => return .cons (← ppExpr x) y z)}"
      Gs.foldlMcps (.mk score l1 l2 : Prod3 _ _ _) (fun e _ (.mk score l1 l2) q => do
        mtrace on .one with s!"[scoreWithGoals] current score {score} for goal {← ppExpr e}"
        let .mk here l1 l2 ← PaIn.genQueryBackNoLoadMain_S l1 l2 inds revCountMax e T.goalPain
        let new := here.foldl score (fun i s => T.goalWeights[i.toNat]! + s)
        q (.mk new l1 l2)
        ) <| fun (.mk score l1 l2) => do
         go l1 l2 more score
    | .node _ _ _ gs _ kids :: more => do
      let Gs ← gs.buildAllS l1 l2 [] 0
      mtrace on .one with s!"[scoreWithGoals] built goals {← Gs.foldlM ListProd.nil (fun x y z => return .cons (← ppExpr x) y z)}"
      Gs.foldlMcps (.mk score l1 l2 : Prod3 _ _ _) (fun e _ (.mk score l1 l2) q => do
        mtrace on .one with s!"[scoreWithGoals] current score {score} for goal {← ppExpr e}"
        let .mk here l1 l2 ← PaIn.genQueryBackNoLoadMain_S l1 l2 inds revCountMax e T.goalPain
        let new := here.foldl score (fun i s => T.goalWeights[i.toNat]! + s)
        q (.mk new l1 l2)
        --if here > score then q here else q score
        -- *note* We could do ↑, but then it would be more adequate to normalize by the maximum weight, not the total weight
        -- The approach ↓ has the defect that the if the same goal is present a multitude of time, it is accounted for a multitude of time
        ) <| fun (.mk score l1 l2) => do
         go l1 l2 (kids.foldl more (fun _ _ x y => x :: y)) score
  mtrace on .one with s!"[scoreWithGoals] loading"
  let .mk score l1 l2 ← go l1 l2 [subIT] 0
  mtrace on .one with s!"[scoreWithGoals] final score {score}"
  let score := score.toFloat / T.goalTotal.toFloat
  mtrace on .one with s!"[scoreWithGoals] noremalised score {score}"
  return .mk score l1 l2


#check 1




def addForwCandidate (l1 : LocalContext) (l2 : LocalInstances)
  (cfg : SearchConfig UInt32Array) (st : SearchState UInt32Array) (sandboxMode : Bool)
  (igc : Nat) (R : ListProd6 Nat ForwCandData Nat ScoreType (thmGenDataEntry UInt32Array) (List (SetTrieP (Nat × Nat) UInt32Array PaIn)))
  (term : Expr) (ugInds : UInt32Array) (thmName : Name ⊕ Nat) (md : ForwMetaData)
  : MetaM (Prod4 Nat (ListProd6 Nat ForwCandData Nat ScoreType (thmGenDataEntry UInt32Array) (List (SetTrieP (Nat × Nat) UInt32Array PaIn))) LocalContext LocalInstances) :=
  do
  mtracing
  let rec a?p (ty : Expr) : ListProd6 Nat ForwCandData Nat ScoreType (thmGenDataEntry UInt32Array) (List (SetTrieP (Nat × Nat) UInt32Array PaIn)) → Bool
    | .nil => false
    | .cons _ D _ _ _ _ more =>
        if D.isProp
        then
          if D.type == ty -- not defeq for speed ??
          then true
          else a?p ty more
        else a?p ty more
  let rec a?np (te : Expr) : ListProd6 Nat ForwCandData Nat ScoreType (thmGenDataEntry UInt32Array) (List (SetTrieP (Nat × Nat) UInt32Array PaIn)) → Bool
    | .nil => false
    | .cons _ D _ _ _ _ more =>
        if D.isProp
        then a?np te more
        else
          if D.term == te -- not defeq for speed ??
          then true
          else a?np te more
    do
    mtrace on .one with s!"[addForwCandidate] on term {← ppExpr term} of type {← ppExpr <| ← inferType term} with ugInds {ugInds}"
    let (incoherent) : Bool :=
      match thmName with
      | .inr i => !(forwCoherentS ugInds i st.introTree)
      | _ => (false)
    if incoherent
    then
      mtrace on .one with s!"[addForwCandidate] incoherent"
      return .mk igc R l1 l2
    else
      let ty ← InferType term l1 l2
      let .mk alreadyDec? l1 ← forwardDuplicateF? l1 ugInds cfg.revCountMax ty st.introTree
      if alreadyDec?
      then
        mtrace on .one with s!"[addForwCandidate] already declared"
        return .mk igc R l1 l2
      else
        let p? ← IsProp ty l1 l2
        let alreadyCand? : Bool :=
          if p? then a?p ty st.forwCandScores else a?np term st.forwCandScores
        if alreadyCand?
        then
          mtrace on .one with s!"[addForwCandidate] already among candiates"
          return .mk igc R l1 l2
        else
          let fwdData : ForwCandData := {isProp := p?, type := ty, term := term, UGinds := ugInds, md := md}
          match thmName with
          | .inr .. =>
              return .mk (igc + 1) (.cons igc fwdData cfg.default_relevance_timer ⟨0,0,cfg.baseLocalThmScore⟩ {} [] R) l1 l2
          | .inl thmN =>
              if sandboxMode
              then
                return .mk (igc + 1) (.cons igc fwdData cfg.default_relevance_timer ⟨0,0,cfg.sandboxModThmScore⟩ {} [] R) l1 l2
              else
                match cfg.regularForw.find? thmN.toString.toUTF8 with
                | .none =>
                    return .mk (igc + 1) (.cons igc fwdData cfg.default_relevance_timer ⟨0, 0, cfg.cachelessThmScore⟩ {} .nil R) l1 l2
                | .some scoredata =>
                    let Q ← mergeLtxForForwIdsS ugInds st.introTree .dead
                    mtrace on .one with s!"[addForwCandidate] relevant ltx : {← Q.ppS l1 l2 [] 0}"
                    let .mk _ fwdscore? pointas ← genQueryForwNoLoadMainS l1 l2 Q scoredata.hypSetTrie
                    let fscore := fwdscore?.foldl (fun r (_,s) => r+s) 0
                    let fscore := fscore.toFloat / scoredata.hypTotal.toFloat
                    mtrace on .one with s!"[addForwCandidate] noremalised forward score {fscore}"
                    let .mk gscore l1 l2 ← scoreWithGoals l1 l2 cfg.revCountMax ugInds scoredata st.introTree
                    mtrace on .one with s!"[addForwCandidate] back score {gscore}"
                    return .mk (igc + 1) (.cons igc fwdData cfg.default_relevance_timer ⟨gscore, fscore,0⟩ scoredata pointas R) l1 l2


/-
**To optimize**:
- maintain PaIn for candiate types and terms so that we can test for candaite duplication more efficiently

-/
#check 1
#check IntroTree.hasForwIdAtGoalId?




def backCoherent (target_goal_id target_forw_id :  Nat)  (IT : IntroTree UInt32Array) :=
  @IntroTree.hasForwIdAtGoalId?
    UInt32Array _ target_goal_id target_forw_id (fun x y => y.oContains x.toUInt32) IT

#check 1

partial def UInt32Array.anyM (a : UInt32Array) (f : Nat → MetaM Bool) : MetaM Bool :=
  let rec go (i : Nat) := do
    if i == a.size
    then return false
    else
      if ← f a[i]!.toNat
      then return true
      else go (i+1)
  go 0

#check 1



def addBackCandidate (l1 : LocalContext) (l2 : LocalInstances)
  (cfg : SearchConfig UInt32Array) (st : SearchState UInt32Array)
  (igc : Nat) (R : ListProd6 Nat BackCandData Nat ScoreType (thmGenDataEntry UInt32Array) (List (SetTrieP (Nat × Nat) UInt32Array PaIn)))
  (ta : ListProd3 Nat Nat Expr) (la : ListProd3 Nat Nat Level)
  (target_goal_id : Nat) (thm : ThmFormat) (res : embedBackData) (rwdata : OptionProd3 rwDirs Expr (List FVarId)) (md : BackStepMetadata)
  : MetaM (Prod Nat (ListProd6 Nat BackCandData Nat ScoreType (thmGenDataEntry UInt32Array) (List (SetTrieP (Nat × Nat) UInt32Array PaIn)))) :=
  do
  mtracing
  let (incoherent) : Bool :=
    match thm.name with
    | .inr ⟨.num _ i⟩ => !(backCoherent target_goal_id i st.introTree)
    | _ => (false)
  if incoherent
  then
    mtrace on .one with s!"[addBackCandidate] incoherent"
    return (igc, R)
  else
    let unis := BackTree.getUnisRequiredFor target_goal_id .empty [st.backTree]
     mtrace on .one with s!"[addBackCandidate] required unis : {unis}"
    -- expects mvarified ta la
    if ← unis.anyM (fun u => unifClashOfComp l1 l2 st.unif_assign ta la u)
    then
      mtrace on .one with s!"[addBackCandidate] clash !"
      return (igc, R)
    else
      let res ← embedBackProcess l1 l2 thm res
      match res with
      | .none =>
        mtrace on .one with s!"[addBackCandidate] embedBackProcess failed"
        return (igc, R)
      | .some _ arg_lvls todo_lvls arg_exprs todo_expr =>
          let bData : BackCandData := ⟨thm, arg_lvls, todo_lvls, arg_exprs, todo_expr, target_goal_id, rwdata,ta,la, md⟩
          match thm.name with
          | .inr .. =>
              return ((igc + 1), .cons igc bData cfg.default_relevance_timer ⟨0,0,cfg.baseLocalThmScore⟩ {} [] R)
          | .inl thmN =>
              if cfg.sandboxMode
              then
                return ((igc + 1), .cons igc bData cfg.default_relevance_timer ⟨0,0,cfg.sandboxModThmScore⟩ {} [] R)
              else
                match cfg.regularBack.find? thmN.toString.toUTF8 with
                | .none =>
                    return ((igc + 1), .cons igc bData cfg.default_relevance_timer ⟨0, 0, cfg.cachelessThmScore⟩ {} .nil R)
                | .some scoredata =>
                    let Q ← mergeLtxForGoalIdS target_goal_id st.introTree
                    mtrace on .one with s!"[addBackCandidate] relevant ltx : {← Q.ppS l1 l2 [] 0}"
                    let .mk _ fwdscore? pointas ← genQueryForwNoLoadMainS l1 l2 Q scoredata.hypSetTrie
                    let fscore := fwdscore?.foldl (fun r (_,s) => r+s) 0
                    let fscore := fscore.toFloat / scoredata.hypTotal.toFloat
                    mtrace on .one with s!"[addBackCandidate] noremalised forward score {fscore}"
                    return ((igc + 1), .cons igc bData cfg.default_relevance_timer ⟨0,fscore,0⟩ scoredata pointas R)


#check unifClashOfComp
#print BackCandData
#check BackTree.getUnisRequiredFor

#check embedBackProcess
