
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrowBeta.Search.IntroTree.Types
import LeanGrowBeta.Utils.Std.List
import LeanGrowBeta.Data.PathIndex.Insert
import LeanGrowBeta.Data.PathIndex.Find
import LeanGrowBeta.Data.PathIndex.Indexing
import LeanGrowBeta.Data.PathIndex.Operations


open Lean Meta

variable {IndexColType : Type}


namespace IntroTree

-- # General

@[specialize]
partial def modGoalIdM {m} [Monad m]
  (contains : Nat → IndexColType → Bool)
  (l1 : LocalContext) (l2 : LocalInstances)
  (target_goal_id : Nat)
  (modGoalIds modForwIds : List Nat → m (List Nat)) (modGoalDirs modForwDirs : IndexColType → m IndexColType)
  (modGoalPI modLtxPI : PaIn IndexColType → LocalContext → LocalInstances → m (Prod3 (PaIn IndexColType) LocalContext LocalInstances))
  (IT : IntroTree IndexColType)
  : m (Prod3 (IntroTree IndexColType) LocalContext LocalInstances) :=
  let rec @[specialize] inner
    (seen : ListProd3 IndexColType IndexColType (IntroTree IndexColType)) :
    ListProd3 IndexColType IndexColType (IntroTree IndexColType) → (OptionProd3 IndexColType IndexColType (IntroTree IndexColType) × ListProd3 IndexColType IndexColType (IntroTree IndexColType))
    | .nil => (.none, seen)
    | .cons gods fods t more =>
        if contains target_goal_id gods
        then (.some gods fods t, seen.foldl more ListProd3.cons)
        else inner (.cons gods fods t seen) more
  match IT with
  | .leaf goids foids goPI foPI => do
    let ⟨A,l1,l2⟩ ← modGoalPI goPI l1 l2
    let ⟨B,l1,l2⟩ ← modLtxPI foPI l1 l2
    return ⟨.leaf (← modGoalIds goids) (← modForwIds foids) A B, l1, l2⟩
  | .node goids foids goPI foPI kidsWdirs => do
      if goids.orderedContains target_goal_id
      then
        let ⟨A,l1,l2⟩ ← modGoalPI goPI l1 l2
        let ⟨B,l1,l2⟩ ← modLtxPI foPI l1 l2
        return ⟨.node (← modGoalIds goids) (← modForwIds foids) A B kidsWdirs, l1, l2⟩
      else
        let (loc,rest) := inner .nil kidsWdirs
        match loc with
        | .none => panic "[modGoalIdM] target {target_goal_id} not found among directions"
        | .some goIs foIs T => do
            let ⟨nT, l1, l2⟩ ← modGoalIdM
              contains l1 l2 target_goal_id modGoalIds modForwIds modGoalDirs modForwDirs modGoalPI modLtxPI T
            let nK := .cons (← modGoalDirs goIs) (← modForwDirs foIs) nT rest
            return ⟨.node goids foids goPI foPI  nK, l1, l2⟩


@[specialize]
partial def modForwIdM {m} [Monad m]
  (contains : Nat → IndexColType → Bool)
  (l1 : LocalContext) (l2 : LocalInstances)
  (target_forw_id : Nat)
  (modGoalIds modForwIds : List Nat → m (List Nat)) (modGoalDirs modForwDirs : IndexColType → m IndexColType)
  (modGoalPI modLtxPI : PaIn IndexColType → LocalContext → LocalInstances → m (Prod3 (PaIn IndexColType) LocalContext LocalInstances))
  (IT : IntroTree IndexColType)
  : m (Prod3 (IntroTree IndexColType) LocalContext LocalInstances) :=
  let rec @[specialize] inner
    (seen : ListProd3 IndexColType IndexColType (IntroTree IndexColType)) :
    ListProd3 IndexColType IndexColType (IntroTree IndexColType) → (OptionProd3 IndexColType IndexColType (IntroTree IndexColType) × ListProd3 IndexColType IndexColType (IntroTree IndexColType))
    | .nil => (.none, seen)
    | .cons gods fods t more =>
        if contains target_forw_id fods
        then (.some gods fods t, seen.foldl more ListProd3.cons)
        else inner (.cons gods fods t seen) more
  match IT with
  | .leaf goids foids goPI foPI => do
    let ⟨A,l1,l2⟩ ← modGoalPI goPI l1 l2
    let ⟨B,l1,l2⟩ ← modLtxPI foPI l1 l2
    return ⟨.leaf (← modGoalIds goids) (← modForwIds foids) A B, l1, l2⟩
  | .node goids foids goPI foPI kidsWdirs => do
      if foids.orderedContains target_forw_id
      then
        let ⟨A,l1,l2⟩ ← modGoalPI goPI l1 l2
        let ⟨B,l1,l2⟩ ← modLtxPI foPI l1 l2
        return ⟨.node (← modGoalIds goids) (← modForwIds foids) A B kidsWdirs, l1, l2⟩
      else
        let (loc,rest) := inner .nil kidsWdirs
        match loc with
        | .none => panic "[modGoalIdM] target {target_goal_id} not found among directions"
        | .some goIs foIs T => do
            let ⟨nT, l1, l2⟩ ← modForwIdM
              contains l1 l2 target_forw_id modGoalIds modForwIds modGoalDirs modForwDirs modGoalPI modLtxPI T
            let nK := .cons (← modGoalDirs goIs) (← modForwDirs foIs) nT rest
            return ⟨.node goids foids goPI foPI  nK, l1, l2⟩


-- /-- write additional specialized code if fold only on one aspect, as else would be inefficient-/
-- @[specialize]
-- partial def foldToGoalId {m} [Monad m]
--   (contains : Nat → IndexColType → Bool)
--   (target_goal_id : Nat)
--   {α β γ δ : Type _} (ini_a : α) (ini_b : β) (ini_c : γ) (ini_d : δ)
--   (foldGoalIds : List Nat → α → m α) (foldForwIds : List Nat → β → m β)
--   (foldGoalPI : PaIn IndexColType → γ → m γ) (foldLtxPI : PaIn IndexColType → δ → m δ)
--   (IT : IntroTree IndexColType)
--   : m (α × β × γ × δ × Option (ListProd3 IndexColType IndexColType (IntroTree IndexColType))) :=
--   let rec @[specialize] inner :
--     ListProd3 IndexColType IndexColType (IntroTree IndexColType) → (OptionProd3 IndexColType IndexColType (IntroTree IndexColType))
--     | .nil => (.none)
--     | .cons gods fods t more =>
--         if contains target_goal_id gods
--         then (.some gods fods t)
--         else inner more
--   match IT with
--   | .leaf goids foids goPI foPI => do
--       return (← foldGoalIds goids ini_a, ← foldForwIds foids ini_b, ← foldGoalPI goPI ini_c, ← foldLtxPI foPI ini_d, .none)
--   | .node goids foids goPI foPI kidsWdirs => do
--       if goids.orderedContains target_goal_id
--       then
--         return (← foldGoalIds goids ini_a, ← foldForwIds foids ini_b, ← foldGoalPI goPI ini_c, ← foldLtxPI foPI ini_d, .some kidsWdirs)
--       else
--         match inner kidsWdirs with
--         | .none => return @panic _ ⟨(ini_a, ini_b, ini_c, ini_d, .none)⟩ "[foldToGoal] target {target_goal_id} not found among directions"
--         | .some _ _ T => do
--             foldToGoalId
--               contains target_goal_id ini_a ini_b ini_c ini_d
--               foldGoalIds foldForwIds foldGoalPI foldLtxPI T


-- /-- write additional specialized code if fold only on one aspect, as else would be inefficient-/
-- @[specialize]
-- partial def foldToForwId {m} [Monad m]
--   (contains : Nat → IndexColType → Bool)
--   (target_forw_id : Nat)
--   {α β γ δ : Type _} (ini_a : α) (ini_b : β) (ini_c : γ) (ini_d : δ)
--   (foldGoalIds : List Nat → α → m α) (foldForwIds : List Nat → β → m β)
--   (foldGoalPI : PaIn IndexColType → γ → m γ) (foldLtxPI : PaIn IndexColType → δ → m δ)
--   (IT : IntroTree IndexColType)
--   : m (α × β × γ × δ × Option (ListProd3 IndexColType IndexColType (IntroTree IndexColType))) :=
--   let rec @[specialize] inner :
--     ListProd3 IndexColType IndexColType (IntroTree IndexColType) → (OptionProd3 IndexColType IndexColType (IntroTree IndexColType))
--     | .nil => (.none)
--     | .cons gods fods t more =>
--         if contains target_forw_id fods
--         then (.some gods fods t)
--         else inner more
--   match IT with
--   | .leaf goids foids goPI foPI => do
--       return (← foldGoalIds goids ini_a, ← foldForwIds foids ini_b, ← foldGoalPI goPI ini_c, ← foldLtxPI foPI ini_d, .none)
--   | .node goids foids goPI foPI kidsWdirs => do
--       if foids.orderedContains target_forw_id
--       then
--         return (← foldGoalIds goids ini_a, ← foldForwIds foids ini_b, ← foldGoalPI goPI ini_c, ← foldLtxPI foPI ini_d, .some kidsWdirs)
--       else
--         match inner kidsWdirs with
--         | .none => return @panic _ ⟨(ini_a, ini_b, ini_c, ini_d, .none)⟩ "[foldToGoal] target {target_goal_id} not found among directions"
--         | .some _ _ T => do
--             foldToForwId
--               contains target_forw_id ini_a ini_b ini_c ini_d
--               foldGoalIds foldForwIds foldGoalPI foldLtxPI T


-- /--
-- Assumes `target_forw_ids` to be consistent
-- write additional specialized code if fold only on one aspect, as else would be inefficient-/
-- @[specialize]
-- partial def foldToForwIds {m} [Monad m]
--   (contains : Nat → IndexColType → Bool)
--   (target_forw_ids : List Nat)
--   {α β γ δ : Type _} (ini_a : α) (ini_b : β) (ini_c : γ) (ini_d : δ)
--   (foldGoalIds : List Nat → α → m α) (foldForwIds : List Nat → β → m β)
--   (foldGoalPI : PaIn IndexColType → γ → m γ) (foldLtxPI : PaIn IndexColType → δ → m δ)
--   (IT : IntroTree IndexColType)
--   : m (α × β × γ × δ × Option (ListProd3 IndexColType IndexColType (IntroTree IndexColType))) :=
--   let target_forw_ids := target_forw_ids.mergeSort
--   let rec @[specialize] inner (dir : Nat) :
--     ListProd3 IndexColType IndexColType (IntroTree IndexColType) → (OptionProd3 IndexColType IndexColType (IntroTree IndexColType))
--     | .nil => (.none)
--     | .cons gods fods t more =>
--         if contains dir fods
--         then (.some gods fods t)
--         else inner dir more
--   match IT with
--   | .leaf goids foids goPI foPI => do
--       return (← foldGoalIds goids ini_a, ← foldForwIds foids ini_b, ← foldGoalPI goPI ini_c, ← foldLtxPI foPI ini_d, .none)
--   | .node goids foids goPI foPI kidsWdirs => do
--       let D := List.orderedDiff target_forw_ids foids
--       match D with
--       | [] =>
--         return (← foldGoalIds goids ini_a, ← foldForwIds foids ini_b, ← foldGoalPI goPI ini_c, ← foldLtxPI foPI ini_d, .some kidsWdirs)
--       | nx :: _ =>
--         match inner nx kidsWdirs with
--         | .none => return @panic _ ⟨(ini_a, ini_b, ini_c, ini_d, .none)⟩ "[foldToGoal] target {target_goal_id} not found among directions"
--         | .some _ _ T => do
--             foldToForwIds
--               contains target_forw_ids ini_a ini_b ini_c ini_d
--               foldGoalIds foldForwIds foldGoalPI foldLtxPI T



-- # Specific


#check PaIn.insert

@[specialize]
def insertGoalsAtGoalId [Repr IndexColType]
  (contains : Nat → IndexColType → Bool) (ofList : List Nat → IndexColType )
  (union : IndexColType → IndexColType → IndexColType) (singleton : Nat → IndexColType)
  (emptyCol : IndexColType) (insert : Nat → IndexColType → IndexColType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (target_goal_id : Nat) (IT : IntroTree IndexColType)
  (newGoals : ListProd Nat Expr)
  : MetaM (Prod3 (IntroTree IndexColType) LocalContext LocalInstances) :=
  let newGoalIds := newGoals.foldl [] (fun x _ y => y.orderedInsertOrLeave x)
  let newGoalIdx := ofList newGoalIds
  IT.modGoalIdM contains l1 l2 target_goal_id
    (fun x => return List.orderedUnion newGoalIds x)
    (pure)
    (fun x => return union newGoalIdx x)
    (pure)
    (fun goPI l1 l2 =>
      newGoals.foldlM ⟨goPI,l1,l2⟩ (fun i e ⟨T,l1,l2⟩ =>
        T.insert l1 l2 e i emptyCol singleton insert)
      )
    (fun x l1 l2 => return ⟨x,l1,l2⟩)


/-- refer to version below-/
@[specialize]
def removeGoalId [Repr IndexColType]
  (contains : Nat → IndexColType → Bool)
  (erase : Nat → IndexColType → IndexColType)
  (difference : IndexColType → IndexColType → IndexColType) (singleton : Nat → IndexColType) (empty? : IndexColType → Bool)
  (emptyCol : IndexColType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (target_goal_id : Nat) (IT : IntroTree IndexColType)
  : MetaM (Prod3 (IntroTree IndexColType) LocalContext LocalInstances) :=
  IT.modGoalIdM contains l1 l2 target_goal_id
    (fun x => return List.orderedEraseOrLeave target_goal_id x)
    (pure)
    (fun x => return erase target_goal_id x)
    (pure)
    (fun goPI l1 l2 =>
      let x := goPI.deleteOfInds (singleton target_goal_id) difference  emptyCol empty?
      return ⟨x,l1,l2⟩)
    (fun x l1 l2 => return ⟨x,l1,l2⟩)



/-- Should be used for unifications to get *active goals*.
Then, then IT still contains organisational information in its index fields,
and the PaIns can be used for unification ; though, the PaIn indices will only
be a subset of of those of the IT field
-/
@[specialize]
def removeGoalIdOnPaInOnly [Repr IndexColType]
  (contains : Nat → IndexColType → Bool)
  (difference : IndexColType → IndexColType → IndexColType) (singleton : Nat → IndexColType)
  (empty? : IndexColType → Bool) (emptyCol : IndexColType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (target_goal_id : Nat) (IT : IntroTree IndexColType)
  : MetaM (Prod3 (IntroTree IndexColType) LocalContext LocalInstances) :=
  IT.modGoalIdM contains l1 l2 target_goal_id
    pure
    (pure)
    pure
    (pure)
    (fun goPI l1 l2 =>
      let x := goPI.deleteOfInds (singleton target_goal_id) difference emptyCol empty?
      return ⟨x,l1,l2⟩)
    (fun x l1 l2 => return ⟨x,l1,l2⟩)

@[specialize]
def insertForwsAtGoalId [Repr IndexColType]
  (contains : Nat → IndexColType → Bool) (ofList : List Nat → IndexColType )
  (union : IndexColType → IndexColType → IndexColType) (singleton : Nat → IndexColType)
  (emptyCol : IndexColType) (insert : Nat → IndexColType → IndexColType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (target_goal_id : Nat) (IT : IntroTree IndexColType)
  (newForws : ListProd Nat Expr)
  : MetaM (Prod3 (IntroTree IndexColType) LocalContext LocalInstances) :=
  let newGoalIds := newForws.foldl [] (fun x _ y => y.orderedInsertOrLeave x)
  let newGoalIdx := ofList newGoalIds
  IT.modGoalIdM contains l1 l2 target_goal_id
    (pure)
    (fun x => return List.orderedUnion newGoalIds x)
    (pure)
    (fun x => return union newGoalIdx x)
    (fun x l1 l2 => return ⟨x,l1,l2⟩)
    (fun goPI l1 l2 =>
      newForws.foldlM ⟨goPI,l1,l2⟩ (fun i e ⟨T,l1,l2⟩ =>
        T.insert l1 l2 e i emptyCol singleton insert)
      )



partial def gatherUGidsToGoalId
  (target_goal_id : Nat)
  (ini : List Nat)
  (IT : IntroTree (List Nat))
  : List Nat :=
  let rec @[specialize] inner :
    ListProd3 (List Nat) (List Nat) (IntroTree (List Nat)) → (OptionProd3 (List Nat) (List Nat) (IntroTree (List Nat)))
    | .nil => (.none)
    | .cons gods fods t more =>
        if gods.orderedContains target_goal_id
        then (.some gods fods t)
        else inner more
  match IT with
  | .leaf _ foids _ _ =>
      List.orderedUnion foids ini
  | .node goids foids _ _ kidsWdirs =>
      if goids.orderedContains target_goal_id
      then
        List.orderedUnion foids ini
      else
        match inner kidsWdirs with
        | .none => panic s!"[gatherUGidsToGoalId] target {target_goal_id} not found among directions"
        | .some _ _ T =>
            gatherUGidsToGoalId target_goal_id (List.orderedUnion foids ini) T


partial def gatherUGidsAtGoalId
  (target_goal_id : Nat)
  (IT : IntroTree (List Nat))
  : List Nat :=
  let rec @[specialize] inner :
    ListProd3 (List Nat) (List Nat) (IntroTree (List Nat)) → (OptionProd3 (List Nat) (List Nat) (IntroTree (List Nat)))
    | .nil => (.none)
    | .cons gods fods t more =>
        if gods.orderedContains target_goal_id
        then (.some gods fods t)
        else inner more
  match IT with
  | .leaf _ foids _ _ => foids
  | .node goids foids _ _ kidsWdirs =>
      if goids.orderedContains target_goal_id
      then
        foids
      else
        match inner kidsWdirs with
        | .none => panic s!"[gatherUGidsToGoalId] target {target_goal_id} not found among directions"
        | .some _ _ T =>
            gatherUGidsAtGoalId target_goal_id T




partial def gatherUGidsToGoalIdStrict
  (target_goal_id : Nat)
  (ini : List Nat)
  (IT : IntroTree (List Nat))
  : List Nat :=
  trace set TracingFlags.none in
  trace on .zero with s!"[gatherUGidsToGoalIdStrict] call on ini {ini} IT {IT.pp 0}" in
  let rec @[specialize] inner :
    ListProd3 (List Nat) (List Nat) (IntroTree (List Nat)) → (OptionProd3 (List Nat) (List Nat) (IntroTree (List Nat)))
    | .nil => (.none)
    | .cons gods fods t more =>
        if gods.orderedContains target_goal_id
        then (.some gods fods t)
        else inner more
  match IT with
  | .leaf _ _ _ _ => ini
  | .node goids foids _ _ kidsWdirs =>
      if goids.orderedContains target_goal_id
      then
        ini
      else
        match inner kidsWdirs with
        | .none => panic s!"[gatherUGidsToGoalId] target {target_goal_id} not found among directions"
        | .some _ _ T =>
            gatherUGidsToGoalIdStrict target_goal_id (List.orderedUnion foids ini) T




@[specialize]
partial def integrateIntro
  [Repr IndexColType]
  (union : IndexColType → IndexColType → IndexColType)
  (contains : Nat → IndexColType → Bool) (ofList : List Nat → IndexColType) (singleton : Nat → IndexColType)
  (emptyCol : IndexColType) (insert : Nat → IndexColType → IndexColType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (spawn_goal_id : Nat) (IT : IntroTree IndexColType) (head_goal_id : Nat) (head_goal : Expr) (newIntroForw : ListProd Nat Expr)
  : MetaM (Prod3 (IntroTree IndexColType) LocalContext LocalInstances) :=
  let rec @[specialize] inner
    (seen : ListProd3 IndexColType IndexColType (IntroTree IndexColType)) :
    ListProd3 IndexColType IndexColType (IntroTree IndexColType) → (OptionProd3 IndexColType IndexColType (IntroTree IndexColType) × ListProd3 IndexColType IndexColType (IntroTree IndexColType))
    | .nil => (.none, seen)
    | .cons gods fods t more =>
        if contains spawn_goal_id gods
        then (.some gods fods t, seen.foldl more ListProd3.cons)
        else inner (.cons gods fods t seen) more
  let rec @[specialize] go
    (newFids : List Nat) (newFidx : IndexColType) (head_goal_idx : IndexColType) (nT nG : PaIn IndexColType)
    (IT : IntroTree IndexColType) (k : IntroTree IndexColType → MetaM (Prod3 (IntroTree IndexColType) LocalContext LocalInstances)) : MetaM (Prod3 (IntroTree IndexColType) LocalContext LocalInstances) :=
    match IT with
    | .leaf goids foids goPI foPI => do
      -- let ngoI := goids.orderedInsertOrLeave head_goal_id
      -- let nfoI := List.orderedUnion foids newFids
      k <| .node goids foids goPI foPI (.cons head_goal_idx newFidx (.leaf [head_goal_id] newFids nG nT) .nil)
    | .node goids foids goPI foPI kidsWdirs => do
        if goids.orderedContains spawn_goal_id
        then
          -- let ngoI := goids.orderedInsertOrLeave head_goal_id
          -- let nfoI := List.orderedUnion foids newFids
          k <| .node goids foids goPI foPI (.cons head_goal_idx newFidx (.leaf [head_goal_id] newFids nG nT) kidsWdirs)
        else
          let (loc,rest) := inner .nil kidsWdirs
          match loc with
          | .none => k <| panic s!"[integrateIntro] target {spawn_goal_id} not found among directions"
          | .some goIs foIs T => do
              go newFids newFidx head_goal_idx nT nG T
                <| fun nT => do
                  -- let ngoI := goids.orderedInsertOrLeave head_goal_id
                  -- let nfoI := List.orderedUnion foids newFids
                  let ngoID := insert head_goal_id goIs
                  let nfoID := union foIs newFidx
                  let nK := .cons ngoID nfoID nT rest
                  k <| .node goids foids goPI foPI  nK
  do
  let newFids := newIntroForw.foldl [] (fun n _ r => r.orderedInsertOrLeave n)
  let newFidx := ofList newFids
  let head_goal_idx := singleton head_goal_id
  let ⟨nT,l1,l2⟩ ← newIntroForw.foldlM (⟨PaIn.dead,l1,l2⟩ : Prod3 _ _ _) (fun i e ⟨R,l1,l2⟩ => do
    R.insert l1 l2 e i emptyCol singleton insert
    )
  let ⟨nG,l1,l2⟩ ← PaIn.dead.insert l1 l2 head_goal head_goal_id emptyCol singleton insert
  go newFids newFidx head_goal_idx nT nG IT (fun x => return ⟨x,l1,l2⟩)




/-- Assumes `target_forw_ids` is consistent, ie. are on a same path on the introtree-/
@[specialize]
partial def insertForwAtForwIds [Repr IndexColType]
  (contains : Nat → IndexColType → Bool) (ofList : List Nat → IndexColType )
  (union : IndexColType → IndexColType → IndexColType) (singleton : Nat → IndexColType)
  (emptyCol : IndexColType) (insert : Nat → IndexColType → IndexColType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (target_forw_ids : List Nat) (IT : IntroTree IndexColType)
  (new_forw_id : Nat) (new_forw : Expr)
  : MetaM (Prod3 (IntroTree IndexColType) LocalContext LocalInstances) :=
    let target_forw_ids := target_forw_ids.mergeSort
    let rec @[specialize] inner (dir : Nat)
      (seen : ListProd3 IndexColType IndexColType (IntroTree IndexColType)) :
      ListProd3 IndexColType IndexColType (IntroTree IndexColType) → (OptionProd3 IndexColType IndexColType (IntroTree IndexColType) × ListProd3 IndexColType IndexColType (IntroTree IndexColType))
      | .nil => (.none, seen)
      | .cons gods fods t more =>
          if contains dir fods
          then (.some gods fods t, seen.foldl more ListProd3.cons)
          else inner dir (.cons gods fods t seen) more
    match IT with
    | .leaf goids foids goPI foPI => do
        let D := List.orderedDiff target_forw_ids foids
        if D.isEmpty
        then
          let ⟨nF,l1,l2⟩ ← foPI.insert l1 l2 new_forw new_forw_id emptyCol singleton insert
          return ⟨.leaf goids (foids.orderedInsertOrLeave new_forw_id) goPI nF,l1,l2⟩
        else throwError s!"[insertForwAtForwIds] reached leaf but {D} remains"
    | .node goids foids goPI foPI kids => do
        let D := List.orderedDiff target_forw_ids foids
        match D with
        | [] =>
          let ⟨nF,l1,l2⟩ ← foPI.insert l1 l2 new_forw new_forw_id emptyCol singleton insert
          return ⟨.node goids (foids.orderedInsertOrLeave new_forw_id) goPI nF kids,l1,l2⟩
        | nx :: _ =>
            let (found,rest) := inner nx .nil kids
            match found with
            | .none => throwError s!"[insertForwAtForwIds] searching for {D}, but not found in directions"
            | .some gods fods t =>
                let ⟨nt,l1,l2⟩ ← insertForwAtForwIds
                  contains ofList union singleton emptyCol insert l1 l2 D t new_forw_id new_forw
                let nfods := insert new_forw_id fods
                -- return ⟨.node goids (foids.orderedInsertOrLeave new_forw_id) goPI foPI (.cons gods nfods nt rest),l1,l2⟩
                return ⟨.node goids foids goPI foPI (.cons gods nfods nt rest),l1,l2⟩



-- # Other

/-- TODO: version that asks about partiular branch of introtree-/
@[specialize]
partial def hasForw? [Repr IndexColType]
  (empty? : IndexColType → Bool) (ofList : List Nat → IndexColType)
  (intersect union : IndexColType → IndexColType → IndexColType) (empty : IndexColType) (revCountMax : Nat)
  (l1 : LocalContext) (l2 : LocalInstances)
  (ce : Expr) (T : IntroTree IndexColType)
  : MetaM (Prod3 Bool LocalContext LocalInstances) :=
  let rec @[specialize] go (l1 : LocalContext) (l2 : LocalInstances) : List (IntroTree IndexColType) → MetaM (Prod3 Bool LocalContext LocalInstances)
    | [] => return ⟨false,l1,l2⟩
    | nx :: more =>
        match nx with
        | .leaf _ is _ ltx => do
            let allIds := ofList is
            let ⟨qase,_,_,l1,l2⟩ ← ltx.findCore l1 l2
              empty? intersect union empty allIds revCountMax
              ce
            if qase == 3
            then return ⟨true,l1,l2⟩
            else go l1 l2 more
        | .node _ is _ ltx kidsWdirs => do
            let allIds := ofList is
            let ⟨qase,_,_,l1,l2⟩ ← ltx.findCore l1 l2
              empty? intersect union empty allIds revCountMax
              ce
            if qase == 3
            then return ⟨true,l1,l2⟩
            else go l1 l2 (kidsWdirs.foldl more (fun _ _ it m => it :: m))
  go l1 l2 [T]



@[specialize]
partial def hasForwAtGoalId? [Repr IndexColType]
  (target_goal_id : Nat)
  (contains : Nat → IndexColType → Bool) (empty? : IndexColType → Bool) (ofList : List Nat → IndexColType)
  (intersect union : IndexColType → IndexColType → IndexColType) (empty : IndexColType) (revCountMax : Nat)
  (l1 : LocalContext) (l2 : LocalInstances)
  (ce : Expr) (T : IntroTree IndexColType)
  : MetaM (Prod3 Bool LocalContext LocalInstances) :=
  let rec @[specialize] inner :
    ListProd3 IndexColType IndexColType (IntroTree IndexColType) → (Option (IntroTree IndexColType))
    | .nil => (.none)
    | .cons gods _ t more =>
        if contains target_goal_id gods
        then (.some t)
        else inner more
  let rec @[specialize] go (l1 : LocalContext) (l2 : LocalInstances) : (IntroTree IndexColType) → MetaM (Prod3 Bool LocalContext LocalInstances)
    | .leaf _ is _ ltx => do
        let allIds := ofList is
        let ⟨qase,_,_,l1,l2⟩ ← ltx.findCore l1 l2
          empty? intersect union empty allIds revCountMax
          ce
        if qase == 3
        then return ⟨true,l1,l2⟩
        else return ⟨false,l1,l2⟩
    | .node _ is _ ltx kidsWdirs => do
        let allIds := ofList is
        let ⟨qase,_,_,l1,l2⟩ ← ltx.findCore l1 l2
          empty? intersect union empty allIds revCountMax
          ce
        if qase == 3
        then return ⟨true,l1,l2⟩
        else
          let nx :=
              match inner kidsWdirs with
              | .some x => x
              | .none => panic s!"[hasForwAtGoalId?] goal {target_goal_id} is not among kidsWdirs"
          go l1 l2 nx
  go l1 l2 T


/-- Assumes `target_forw_ids` is consistent, ie. are on a same path on the introtree-/
@[specialize]
partial def hasForwEAtForwIds? [Repr IndexColType]
  (empty? : IndexColType → Bool) (ofList : List Nat → IndexColType)
  (toList : IndexColType → List Nat)
  (intersect union : IndexColType → IndexColType → IndexColType) (empty : IndexColType) (revCountMax : Nat)
  (l1 : LocalContext) (l2 : LocalInstances)
  (target_forw_ids : List Nat) (ce : Expr) (IT : IntroTree IndexColType)
  : MetaM (Prod3 Bool LocalContext LocalInstances) :=
  let target_forw_ids := target_forw_ids.mergeSort
  let rec @[specialize] inner (target_forw_ids : List Nat) :
    ListProd3 IndexColType IndexColType (IntroTree IndexColType) → (Option (IntroTree IndexColType))
    | .nil => (.none)
    | .cons _ foIds t more =>
        let I := toList foIds
        if (List.orderedDiff target_forw_ids I).isEmpty
        then
          (.some t)
        else
          inner target_forw_ids more
  let rec @[specialize] go (l1 : LocalContext) (l2 : LocalInstances) (target_forw_ids : List Nat) : (IntroTree IndexColType) → MetaM (Prod3 Bool LocalContext LocalInstances)
    | .leaf _ is _ ltx => do
        let allIds := ofList is
        let ⟨qase,_,_,l1,l2⟩ ← ltx.findCore l1 l2
          empty? intersect union empty allIds revCountMax
          ce
        if qase == 3
        then return ⟨true,l1,l2⟩
        else return ⟨false,l1,l2⟩
    | .node _ is _ ltx kidsWdirs => do
        let allIds := ofList is
        let ⟨qase,_,_,l1,l2⟩ ← ltx.findCore l1 l2
          empty? intersect union empty allIds revCountMax
          ce
        if qase == 3
        then return ⟨true,l1,l2⟩
        else
          let nx := (List.orderedDiff target_forw_ids is)
          match nx with
          | [] => return ⟨false,l1,l2⟩
          | _ =>
            match inner nx kidsWdirs with
            | .some x => go l1 l2 nx x
            | .none => panic s!"[hasForwEAtForwIds?] forws {nx} is not among kidsWdirs"
  go l1 l2 target_forw_ids IT


/-- Assumes `target_forw_ids` is consistent, ie. are on a same path on the introtree-/
@[specialize]
partial def forwCoherent? [Repr IndexColType]
  (toList : IndexColType → List Nat)
  (target_forw_ids : List Nat) (forwI : Nat) (IT : IntroTree IndexColType)
  : Bool :=
  let target_forw_ids := target_forw_ids.mergeSort
  let rec @[specialize] inner (target_forw_ids : List Nat) :
    ListProd3 IndexColType IndexColType (IntroTree IndexColType) → (Option (IntroTree IndexColType))
    | .nil => (.none)
    | .cons _ foIds t more =>
        let I := toList foIds
        if (List.orderedDiff target_forw_ids I).isEmpty
        then
          (.some t)
        else
          inner target_forw_ids more
  let rec @[specialize] go (target_forw_ids : List Nat) : (IntroTree IndexColType) → Bool
    | .leaf _ is _ _ => is.orderedContains forwI
    | .node _ is _ _ kidsWdirs =>
        if is.orderedContains forwI
        then true
        else
          let nx := (List.orderedDiff target_forw_ids is)
          match nx with
          | [] => false
          | _ =>
              match inner nx kidsWdirs with
              | .some x => go nx x
              | .none => panic s!"[forwCoherent?] forws {nx} is not among kidsWdirs"
  go target_forw_ids IT


/-- Assumes `target_forw_ids` is consistent, ie. are on a same path on the introtree-/
@[specialize]
partial def forwGoalCoherent? [Repr IndexColType]
  (toList : IndexColType → List Nat)
  (target_forw_ids : List Nat) (goalI : Nat) (IT : IntroTree IndexColType)
  : Bool :=
  let target_forw_ids := target_forw_ids.mergeSort
  let rec @[specialize] inner (target_forw_ids : List Nat) :
    ListProd3 IndexColType IndexColType (IntroTree IndexColType) → (Option (IntroTree IndexColType))
    | .nil => (.none)
    | .cons _ foIds t more =>
        let I := toList foIds
        if (List.orderedDiff target_forw_ids I).isEmpty
        then
          (.some t)
        else
          inner target_forw_ids more
  let rec @[specialize] go (target_forw_ids : List Nat) : (IntroTree IndexColType) → Bool
    | .leaf is _ _ _ => is.orderedContains goalI
    | .node is Is _ _ kidsWdirs =>
        if is.orderedContains goalI
        then true
        else
          let nx := (List.orderedDiff target_forw_ids Is)
          match nx with
          | [] => false
          | _ =>
              match inner nx kidsWdirs with
              | .some x => go nx x
              | .none => panic s!"[forwGoalCoherent?] forws {nx} is not among kidsWdirs"
  go target_forw_ids IT



@[specialize]
partial def hasGoal? [Repr IndexColType]
  (empty? : IndexColType → Bool) (ofList : List Nat → IndexColType)
  (intersect union : IndexColType → IndexColType → IndexColType) (empty : IndexColType) (revCountMax : Nat)
  (l1 : LocalContext) (l2 : LocalInstances)
  (ce : Expr) (T : IntroTree IndexColType) : MetaM (Prod3 Bool LocalContext LocalInstances) :=
  let rec @[specialize] go (l1 : LocalContext) (l2 : LocalInstances) : List (IntroTree IndexColType) → MetaM (Prod3 Bool LocalContext LocalInstances)
    | [] => return ⟨false,l1,l2⟩
    | nx :: more =>
        match nx with
        | .leaf is _ _ ltx => do
            let allIds := ofList is
            let ⟨qase,_,_,l1,l2⟩ ← ltx.findCore l1 l2
              empty? intersect union empty allIds revCountMax
              ce
            if qase == 3
            then return ⟨true,l1,l2⟩
            else go l1 l2 more
        | .node is _ _ ltx kidsWdirs => do
            let allIds := ofList is
            let ⟨qase,_,_,l1,l2⟩ ← ltx.findCore l1 l2
              empty? intersect union empty allIds revCountMax
              ce
            if qase == 3
            then return ⟨true,l1,l2⟩
            else go l1 l2 (kidsWdirs.foldl more (fun _ _ it m => it :: m))
  go l1 l2 [T]


-- somehow the right one for assembly
@[specialize]
partial def mergeLtxForGoalId {m} [Monad m] [Repr IndexColType]
  (contains : Nat → IndexColType → Bool)
  (union : IndexColType → IndexColType → IndexColType) (emptyCol : IndexColType)
  (target_goal_id : Nat)
  (IT : IntroTree IndexColType)
  (init : PaIn IndexColType)
  : m (PaIn IndexColType) :=
  let rec @[specialize] inner :
    ListProd3 IndexColType IndexColType (IntroTree IndexColType) → (OptionProd3 IndexColType IndexColType (IntroTree IndexColType))
    | .nil => (.none)
    | .cons gods fods t more =>
        if contains target_goal_id gods
        then (.some gods fods t)
        else inner more
  match IT with
  | .leaf _ _ _ foPI => do
      return PaIn.merge union emptyCol foPI init
  | .node goids _ _ foPI kidsWdirs => do
      if goids.orderedContains target_goal_id
      then
        return PaIn.merge union emptyCol foPI init
      else
        match inner kidsWdirs with
        | .none => return panic s!"[mergeLtxForGoalId] target {target_goal_id} not found among directions"
        | .some _ _ T => do
            mergeLtxForGoalId
              contains union emptyCol target_goal_id T init


-- the right one for unification at backsteps
@[specialize]
partial def mergeLtxForGoalIdTruely {m} [Monad m] [Repr IndexColType]
  (contains : Nat → IndexColType → Bool)
  (union : IndexColType → IndexColType → IndexColType) (emptyCol : IndexColType)
  (target_goal_id : Nat)
  (IT : IntroTree IndexColType)
  (init : PaIn IndexColType)
  : m (PaIn IndexColType) :=
  let rec @[specialize] inner :
    ListProd3 IndexColType IndexColType (IntroTree IndexColType) → (OptionProd3 IndexColType IndexColType (IntroTree IndexColType))
    | .nil => (.none)
    | .cons gods fods t more =>
        if contains target_goal_id gods
        then (.some gods fods t)
        else inner more
  match IT with
  | .leaf _ _ _ foPI => do
      return PaIn.merge union emptyCol foPI init
  | .node goids _ _ foPI kidsWdirs => do
      if goids.orderedContains target_goal_id
      then
        return PaIn.merge union emptyCol foPI init
      else
        match inner kidsWdirs with
        | .none => return panic s!"[mergeLtxForGoalIdTruely] target {target_goal_id} not found among directions"
        | .some _ _ T => do
            mergeLtxForGoalIdTruely
              contains union emptyCol target_goal_id T (PaIn.merge union emptyCol foPI init)



@[specialize]
partial def mergeLtxForForwIds {m} [Monad m] [Repr IndexColType]
  (toList : IndexColType → List Nat)
  (union : IndexColType → IndexColType → IndexColType) (emptyCol : IndexColType)
  (target_forw_ids : List Nat)
  (IT : IntroTree IndexColType)
  (init : PaIn IndexColType)
  : m (PaIn IndexColType) :=
  let target_forw_ids := target_forw_ids.mergeSort
  let rec @[specialize] inner (target_forw_ids : List Nat) :
    ListProd3 IndexColType IndexColType (IntroTree IndexColType) → (Option (IntroTree IndexColType))
    | .nil => (.none)
    | .cons _ foIds t more =>
        let I := toList foIds
        if (List.orderedDiff target_forw_ids I).isEmpty
        then
          (.some t)
        else
          inner target_forw_ids more
  match IT with
  | .leaf _ _ _ foPI => do
      return PaIn.merge union emptyCol foPI init
  | .node _ foIds _ foPI kidsWdirs => do
      let nx := (List.orderedDiff target_forw_ids foIds)
      if nx.isEmpty
      then
        return PaIn.merge union emptyCol foPI init
      else
        match inner nx kidsWdirs with
        | .none => return panic s!"[mergeLtxForForwIds] target {target_forw_ids} not found among directions"
        | .some T => mergeLtxForForwIds toList union emptyCol target_forw_ids T init



@[specialize]
partial def mergeGoalsForForwId [Repr IndexColType]
  (contains : Nat → IndexColType → Bool)
  (union : IndexColType → IndexColType → IndexColType) (emptyCol : IndexColType)
  (target_gu_id : Nat)
  (IT : IntroTree IndexColType)
  : PaIn IndexColType :=
  let rec @[specialize] inner :
    ListProd3 IndexColType IndexColType (IntroTree IndexColType) → (Option (IntroTree IndexColType))
    | .nil => (.none)
    | .cons _ fods t more =>
        if contains target_gu_id fods
        then (.some t)
        else inner more
  let rec @[specialize] locate : IntroTree IndexColType → IntroTree IndexColType
    | x@(.leaf ..) => x
    | x@(.node _ foIds _ _ kidsWdirs) =>
        if foIds.orderedContains target_gu_id
        then x
        else
          match inner kidsWdirs with
          | .none => panic s!"[mergeGoalsForForwId] target {target_gu_id} not found among directions"
          | .some T => locate T
  let subIT := locate IT
  let rec go (t : PaIn IndexColType) : List (IntroTree IndexColType) → PaIn IndexColType
    | [] => t
    | .leaf _ _ gs _ :: more => go (PaIn.merge union emptyCol gs t) more
    | .node _ _ gs _ kids :: more => go (PaIn.merge union emptyCol gs t) (kids.foldl more (fun _ _ k R => k :: R))
  go .dead [subIT]

@[specialize]
partial def mergeGoalsForForwIds [Repr IndexColType]
  (toList : IndexColType → List Nat) (union : IndexColType → IndexColType → IndexColType) (emptyCol : IndexColType)
  (target_forw_ids : List Nat)
  (IT : IntroTree IndexColType)
  : PaIn IndexColType :=
  let target_forw_ids := target_forw_ids.mergeSort
  let rec @[specialize] inner (target_forw_ids : List Nat) :
    ListProd3 IndexColType IndexColType (IntroTree IndexColType) → (Option (IntroTree IndexColType))
    | .nil => (.none)
    | .cons _ foIds t more =>
        let I := toList foIds
        if (List.orderedDiff target_forw_ids I).isEmpty
        then
          (.some t)
        else
          inner target_forw_ids more
  let rec @[specialize] locate (target_forw_ids : List Nat) : IntroTree IndexColType → IntroTree IndexColType
    | x@(.leaf ..) => x
    | x@(.node _ foIds _ _ kidsWdirs) =>
        let nx := (List.orderedDiff target_forw_ids foIds)
        match nx with
        | [] => x
        | _ =>
          match inner nx kidsWdirs with
          | .none => panic s!"[mergeGoalsForForwIds] target {target_forw_ids} not found among directions"
          | .some T => locate nx T
  let subIT := locate target_forw_ids IT
  let rec go (t : PaIn IndexColType) : List (IntroTree IndexColType) → PaIn IndexColType
    | [] => t
    | .leaf _ _ gs _ :: more => go (PaIn.merge union emptyCol gs t) more
    | .node _ _ gs _ kids :: more => go (PaIn.merge union emptyCol gs t) (kids.foldl more (fun _ _ k R => k :: R))
  go .dead [subIT]


/-- Assumes `target_forw_ids` is consistent, ie. are on a same path on the introtree-/
@[specialize]
partial def forwIdsFromforwId
  (target_forw_ids : List Nat)
  (IT : IntroTree (List Nat))
  : List Nat :=
  let target_forw_ids := target_forw_ids.mergeSort
  let rec inner (target_forw_ids : List Nat) :
    ListProd3 (List Nat) (List Nat) (IntroTree (List Nat)) → (Option (IntroTree (List Nat)))
    | .nil => (.none)
    | .cons _ fods t more =>
        -- dbg_trace s!"[forwIdsFromforwId] fods {fods}"
        if (List.orderedDiff target_forw_ids fods).isEmpty
        then (.some t)
        else inner target_forw_ids more
  let rec locate (target_forw_ids : List Nat) (done : List Nat) : IntroTree (List Nat) → (List Nat × IntroTree (List Nat))
    | x@(.leaf ..) => (done, x)
    | x@(.node _ foIds _ _ kidsWdirs) =>
        -- dbg_trace s!"[forwIdsFromforwId] target_forw_ids {target_forw_ids} foIds {foIds}"
        let next := (List.orderedDiff target_forw_ids foIds)
        -- dbg_trace s!"[forwIdsFromforwId] next {next}"
        if next.isEmpty
        then (done, x)
        else
          match inner next kidsWdirs with
          | .none => panic s!"[forwIdsFromforwId] target {target_forw_ids} not found among directions"
          | .some T => locate next (foIds.orderedUnion done) T
  let (fromRoot,subIT) := locate target_forw_ids [] IT
  let rec go (done : List Nat) : List (IntroTree (List Nat)) → (List Nat)
    | [] => done
    | .leaf _ fo _ _ :: more => go (List.orderedUnion fo done) more
    | .node _ fo _ _ kids :: more => go (List.orderedUnion fo done) (kids.foldl more (fun _ _ k R => k :: R))
  go fromRoot [subIT]



@[specialize]
partial def topGoalForForwId
  (target_forw_id : Nat)
  (IT : IntroTree (List Nat))
  : Nat × Expr :=
  let rec inner :
    ListProd3 (List Nat) (List Nat) (IntroTree (List Nat)) → (Option (IntroTree (List Nat)))
    | .nil => (.none)
    | .cons _ fods t more =>
        if (fods.orderedContains target_forw_id)
        then (.some t)
        else inner  more
  let rec go : IntroTree (List Nat) → Nat × Expr
    | .leaf goi fo goalPI _  =>
        if fo.orderedContains target_forw_id
        then
          match goi.head? with
          | .none => panic s!"[topGoalForForwId] goal indices are empty !"
          | .some h =>
              let terms := goalPI.buildS [] 0 [h]
              match terms with
              | .nil => panic s!"[topGoalForForwId] goal {h} isn't contained in path index of goals ..."
              | .cons e _ _ => (h,e)
        else
          panic s!"[topGoalForForwId] arrived at leaf but didin't find forw id {target_forw_id}"
    | .node goi fo goalPI _ kids =>
        if fo.orderedContains target_forw_id
        then
          match goi.head? with
          | .none => panic s!"[topGoalForForwId] goal indices are empty !"
          | .some h =>
              let terms := goalPI.buildS [] 0 [h]
              match terms with
              | .nil => panic s!"[topGoalForForwId] goal {h} isn't contained in path index of goals ..."
              | .cons e _ _ => (h,e)
        else
          match inner kids with
          | .none => panic s!"[topGoalForForwId] didn't find forw id {target_forw_id} in kids of node"
          | .some t => go t
  go IT


@[specialize]
partial def hasForwIdAtGoalId? [Repr IndexColType]
  (target_goal_id target_forw_id : Nat)
  (contains : Nat → IndexColType → Bool)
  (T : IntroTree IndexColType) : Bool :=
  let rec @[specialize] inner :
    ListProd3 IndexColType IndexColType (IntroTree IndexColType) → (Option (IntroTree IndexColType))
    | .nil => (.none)
    | .cons gods _ t more =>
        if contains target_goal_id gods
        then (.some t)
        else inner more
  let rec @[specialize] go : (IntroTree IndexColType) →  Bool
    | .leaf _ is _ _ =>
        is.orderedContains target_forw_id
    | .node _ is _ _ kidsWdirs =>
        if is.orderedContains target_forw_id
        then  true
        else
          match inner kidsWdirs with
          | .none => false --panic s!"[hasForwIdAtGoalId?] didn find {target_goal_id} among kids"
          | .some t => go t
  go T


partial def getGoalOfGoalId
  (target_goal_id : Nat)
  (T : IntroTree (List Nat)) : Expr :=
  let rec inner :
    ListProd3 (List Nat) (List Nat) (IntroTree (List Nat)) → (Option (IntroTree (List Nat)))
    | .nil => (.none)
    | .cons gods _ t more =>
        if List.orderedContains target_goal_id gods
        then (.some t)
        else inner more
  let rec go : (IntroTree (List Nat)) →  Expr
    | .leaf _ _ gs _ =>
        match gs.buildS [] 0 [target_goal_id] with
        | .cons e _ _ => e
        | _ => panic s!"[getGoalOfGoalId] build of {target_goal_id} failed"
    | .node is _ gs _ kidsWdirs =>
        if is.orderedContains target_goal_id
        then
          match gs.buildS [] 0 [target_goal_id] with
          | .cons e _ _ => e
          | _ => panic s!"[getGoalOfGoalId] build of {target_goal_id} failed"
        else
          match inner kidsWdirs with
          | .none => panic s!"[getGoalOfGoalId] didn find {target_goal_id} among kids"
          | .some t => go t
  go T
