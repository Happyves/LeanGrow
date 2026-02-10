
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrowBeta.Search.API.IntegrateForw
import LeanGrowBeta.Search.API.IntegrateBack
import LeanGrowBeta.Search.IntroTree.Operations
import LeanGrowBeta.Search.BackTree.Operations
import LeanGrowBeta.Core.GeneralisePaIn.GenQueryForw
import LeanGrowBeta.Core.GeneralisePaIn.GenQueryBack
import LeanGrowBeta.Core.Embedding.EmbedProcessBack


open Lean Meta


#check IntroTree.mergeGoalsForForwIds
#check IntroTree.mergeLtxForForwIds

def mergeGoalsForForwIdsS := IntroTree.mergeGoalsForForwIds id (List.orderedUnion)

#check 1

def mergeLtxForForwIdsS {m : Type → Type _} [Monad m]
  (target_forw_ids : List Nat) (IT : IntroTree (List Nat)) (init : PaIn (List Nat))
  : m (PaIn (List Nat)) :=
  @IntroTree.mergeLtxForForwIds (List Nat) m _ _ id (List.orderedUnion) [] target_forw_ids IT init


#check 1

#check PaIn.genQueryForwWiLoadMain

def genQueryForwWiLoadMainS :=
  @PaIn.genQueryForwWiLoadMain (List Nat) _
    (List.orderedIntersect) (List.orderedDiff) List.isEmpty

#check PaIn.genQueryBackMain
-- where we should load the first time as in
#check PaIn.genQueryBackWiLoadMain



def genQueryBackMainS  :=
  @PaIn.genQueryBackMain (List Nat) _ _ _
    id List.isEmpty (List.orderedIntersect) (List.orderedUnion) []


#check 1

def forwCoherentS (target_forw_ids : List Nat) (forwI : Nat) (IT : IntroTree (List Nat)) :=
  @IntroTree.forwCoherent? (List Nat) _ id target_forw_ids forwI IT

#check 1

-- #exit

partial def scoreWithGoals (l1 : LocalContext) (l2 : LocalInstances)
  (revCountMax : Nat) (target_forw_ids : List Nat) (T : CPaIn (List Nat)) (IT : IntroTree (List Nat))
  : MetaM (Prod3 Float LocalContext LocalInstances) :=
  -- trace set Tracing.Flags.none in do
  let rec @[specialize] inner (target_forw_ids : List Nat) :
    ListProd3 (List Nat) (List Nat) (IntroTree (List Nat)) → (Option (IntroTree (List Nat)))
    | .nil => (.none)
    | .cons _ foIds t more =>
        let I := foIds
        if (List.orderedDiff target_forw_ids I).isEmpty
        then
          (.some t)
        else
          inner target_forw_ids more
  let rec @[specialize] locate (target_forw_ids : List Nat) : IntroTree (List Nat) → IntroTree (List Nat)
    | x@(.leaf ..) => x
    | x@(.node _ foIds _ _ kidsWdirs) =>
        let nx := (List.orderedDiff target_forw_ids foIds)
        match nx with
        | [] => x
        | _ =>
          match inner nx kidsWdirs with
          | .none => panic s!"[mergeGoalsForForwIds] target {target_forw_ids} not found among directions"
          | .some T => locate nx T
  do
  mtrace on .one with s!"[scoreWithGoals] locating subtree for {target_forw_ids}, whithin {IT.pp 0}"
  let subIT := locate target_forw_ids IT
  mtrace on .one with s!"[scoreWithGoals] found {subIT.pp 0}"
  let inds := T.pi.getIndicesS
  let rec go (l1 : LocalContext) (l2 : LocalInstances) (it : List (IntroTree (List Nat))) (score : Float) : MetaM (Prod3 Float LocalContext LocalInstances) := do
    match it with
    | [] => return .mk score l1 l2
    | .leaf _ _ gs _ :: more => do
      let Gs := gs.buildAllS [] 0
      mtrace on .one with s!"[scoreWithGoals] built goals {← Gs.foldlM ListProd.nil (fun x y z => return .cons (← ppExpr x) y z)}"
      Gs.foldlMcps (.mk score l1 l2 : Prod3 _ _ _) (fun e _ (.mk score l1 l2) q => do
        mtrace on .one with s!"[scoreWithGoals] current score {score} for goal {← ppExpr e}"
        let .mk here? l1 l2 ← genQueryBackMainS l1 l2 inds revCountMax e T.pi T.weights
        match here? with
        | .none => q (.mk score l1 l2)
        | .some here =>
            mtrace on .one with s!"[scoreWithGoals] here {here}"
            q (.mk (here + score) l1 l2)
            -- see note ↓
        ) <| fun (.mk score l1 l2) => do
         go l1 l2 more score
    | .node _ _ gs _ kids :: more => do
      let Gs := gs.buildAllS [] 0
      mtrace on .one with s!"[scoreWithGoals] built goals {← Gs.foldlM ListProd.nil (fun x y z => return .cons (← ppExpr x) y z)}"
      Gs.foldlMcps (.mk score l1 l2 : Prod3 _ _ _) (fun e _ (.mk score l1 l2) q => do
        mtrace on .one with s!"[scoreWithGoals] current score {score} for goal {← ppExpr e}"
        let .mk here? l1 l2 ← genQueryBackMainS l1 l2 inds revCountMax e T.pi T.weights
        match here? with
        | .none => q (.mk score l1 l2)
        | .some here =>
            mtrace on .one with s!"[scoreWithGoals] here {here}"
            q (.mk (here + score) l1 l2)
                --if here > score then q here else q score
                -- *note* We could do ↑, but then it would be more adequate to normalize by the maximum weight, not the total weight
                -- The approach ↓ has the defect that the if the same goal is present a multitude of time, it is accounted for a multitude of time
        ) <| fun (.mk score l1 l2) => do
         go l1 l2 (kids.foldl more (fun _ _ x y => x :: y)) score
  mtrace on .one with s!"[scoreWithGoals] loading"
  for data in T.loadData do
    for j in [:data.lvlNum] do
      let _ ← mkLevelMVarOfName (lnode data.sampleName j 0)
    let mut i := 0
    for T in data.types do
      let _ ← mkMvarStdWiCoI (lnode data.sampleName i 0) T l1 l2
      i := i+1
  let .mk score l1 l2 ← go l1 l2 [subIT] 0
  mtrace on .one with s!"[scoreWithGoals] final score {score}"
  let score := score / T.totalWeight
  mtrace on .one with s!"[scoreWithGoals] noremalised score {score}"
  return .mk score l1 l2


#check 1




def addForwCandidate (l1 : LocalContext) (l2 : LocalInstances)
  (cfg : SearchConfig) (st : SearchState (List Nat)) (sandboxMode : Bool)
  (igc : Nat) (R : ListProd6 Nat ForwCandData Nat ScoreType (CPaIn (List Nat)) (List (CSetTrie  (List Nat) Nat)))
  (term : Expr) (ugInds : List Nat) (thmName : Name ⊕ Nat) (md : ForwMetaData)
  : MetaM (Prod4 Nat (ListProd6 Nat ForwCandData Nat ScoreType (CPaIn (List Nat)) (List (CSetTrie  (List Nat) Nat))) LocalContext LocalInstances) :=
  -- trace set Tracing.Flags.none in
  let rec a?p (ty : Expr) : ListProd6 Nat ForwCandData Nat ScoreType (CPaIn (List Nat)) (List (CSetTrie  (List Nat) Nat)) → Bool
    | .nil => false
    | .cons _ D _ _ _ _ more =>
        if D.isProp
        then
          if D.type == ty -- not defeq for speed ??
          then true
          else a?p ty more
        else a?p ty more
  let rec a?np (te : Expr) : ListProd6 Nat ForwCandData Nat ScoreType (CPaIn (List Nat)) (List (CSetTrie  (List Nat) Nat)) → Bool
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
      let .mk alreadyDec? l1 l2 ← forwardDuplicateF? l1 l2 ugInds cfg.revCountMax ty st.introTree
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
              return .mk (igc + 1) (.cons igc fwdData cfg.default_relevance_timer ⟨0,0,cfg.baseLocalThmScore⟩ (CPaIn.empty (List Nat)) [] R) l1 l2
          | .inl thmN =>
              if sandboxMode
              then
                return .mk (igc + 1) (.cons igc fwdData cfg.default_relevance_timer ⟨0,0,cfg.sandboxModThmScore⟩ (CPaIn.empty (List Nat)) [] R) l1 l2
              else
                match cfg.thmPatternScores.find? thmN.toString.toUTF8 with
                | .none =>
                    return .mk (igc + 1) (.cons igc fwdData cfg.default_relevance_timer ⟨0, 0, cfg.cachelessThmScore⟩ (.empty _) .nil R) l1 l2
                | .some scoredata =>
                    let Q ← mergeLtxForForwIdsS ugInds st.introTree .dead
                    mtrace on .one with s!"[addForwCandidate] relevant ltx : {← Q.ppS l1 l2 [] 0}"
                    let sts := scoredata.2
                    let .mk _ fwdscore? pointas ← genQueryForwWiLoadMainS l1 l2 sts.loadData sts.weights sts.samHypDict Q sts.settrie
                    let fscore := match fwdscore? with | .none => 0 | .some s => s / sts.totalWeight
                    mtrace on .one with s!"[addForwCandidate] noremalised forward score {fscore}"
                    let pointas : List (CSetTrie (List Nat) Nat) := pointas.foldl (fun R s => ⟨s, sts.loadData, sts.weights, sts.totalWeight, sts.samHypDict⟩ :: R ) []
                    let .mk gscore l1 l2 ← scoreWithGoals l1 l2 cfg.revCountMax ugInds scoredata.1 st.introTree
                    mtrace on .one with s!"[addForwCandidate] back score {gscore}"
                    return .mk (igc + 1) (.cons igc fwdData cfg.default_relevance_timer ⟨gscore, fscore,0⟩ scoredata.1 pointas R) l1 l2


/-
**To optimize**:
- maintain PaIn for candiate types and terms so that we can test for candaite duplication more efficiently

-/
#check 1




def backCoherent (target_goal_id target_forw_id :  Nat)  (IT : IntroTree (List Nat)) :=
  @IntroTree.hasForwIdAtGoalId? (List Nat) _ target_goal_id target_forw_id (List.orderedContains) IT

#check 1

def addBackCandidate (l1 : LocalContext) (l2 : LocalInstances)
  (cfg : SearchConfig) (st : SearchState (List Nat))
  (igc : Nat) (R : ListProd5 Nat BackCandData Nat ScoreType (List (CSetTrie  (List Nat) Nat)))
  (ta : ListProd3 Nat Nat Expr) (la : ListProd3 Nat Nat Level)
  (target_goal_id : Nat) (thm : ThmFormat) (res : embedBackData) (rwdata : OptionProd3 rwDirs Expr (List FVarId)) (md : BackStepMetadata)
  : MetaM (Prod Nat (ListProd5 Nat BackCandData Nat ScoreType (List (CSetTrie  (List Nat) Nat)))) :=
  -- trace set Tracing.Flags.none in
  do
  let (incoherent) : Bool :=
    match thm.name with
    | .inr ⟨.num _ i⟩ => !(backCoherent target_goal_id i st.introTree)
    | _ => (false)
  if incoherent
  then
    mtrace on .one with s!"[addBackCandidate] incoherent"
    return (igc, R)
  else
    let unis := BackTree.getUnisRequiredFor target_goal_id [] [st.backTree]
     mtrace on .one with s!"[addBackCandidate] required unis : {unis}"
    -- expects mvarified ta la
    if ← unis.anyM (fun u => unifClashOfComp l1 l2 st.unif_assign ta la u)
    then
      mtrace on .one with s!"[addBackCandidate] clash !"
      return (igc, R)
    else
      embedBackProcess l1 l2 thm res
        (do mtrace on .one with s!"[addBackCandidate] embedBackProcess failed" ; return (igc, R))
        <| fun _ arg_lvls todo_lvls arg_exprs todo_expr => do
          let bData : BackCandData := ⟨thm, arg_lvls, todo_lvls, arg_exprs, todo_expr, target_goal_id, rwdata,ta,la, md⟩
          match thm.name with
          | .inr .. =>
              return ((igc + 1), .cons igc bData cfg.default_relevance_timer ⟨0,0,cfg.baseLocalThmScore⟩ [] R)
          | .inl thmN =>
              if cfg.sandboxMode
              then
                return ((igc + 1), .cons igc bData cfg.default_relevance_timer ⟨0,0,cfg.sandboxModThmScore⟩ [] R)
              else
                match cfg.thmPatternScores.find? thmN.toString.toUTF8 with
                | .none =>
                    return ((igc + 1), .cons igc bData cfg.default_relevance_timer ⟨0, 0, cfg.cachelessThmScore⟩ .nil R)
                | .some scoredata =>
                    let Q ← mergeLtxForGoalIdS target_goal_id st.introTree
                    mtrace on .one with s!"[addBackCandidate] relevant ltx : {← Q.ppS l1 l2 [] 0}"
                    let sts := scoredata.3
                    let .mk _ fwdscore? pointas ← genQueryForwWiLoadMainS l1 l2 sts.loadData sts.weights sts.samHypDict Q sts.settrie
                    let fscore := match fwdscore? with | .none => 0 | .some s => s / sts.totalWeight
                    mtrace on .one with s!"[addBackCandidate] noremalised forward score {fscore}"
                    let pointas : List (CSetTrie (List Nat) Nat) := pointas.foldl (fun R s => ⟨s, sts.loadData, sts.weights, sts.totalWeight, sts.samHypDict⟩ :: R ) []
                    return ((igc + 1), .cons igc bData cfg.default_relevance_timer ⟨0,fscore,0⟩ pointas R)


#check unifClashOfComp
#print BackCandData
#check BackTree.getUnisRequiredFor

#check embedBackProcess
