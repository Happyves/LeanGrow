
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Search.IntroTree.Types
import LeanGrow.Src.Utils.Std.List
import LeanGrow.Src.Data.PathIndexG.Insert
import LeanGrow.Src.Data.PathIndexG.Find
import LeanGrow.Src.Data.PathIndexG.Indexing
import LeanGrow.Src.Data.PathIndexG.Operations


open Lean Meta

variable {IndexColType : Type} [Inhabited IndexColType]


namespace IntroTree

-- # General

@[specialize]
partial def modGoalIdM {m} [Monad m]
  (contains : Nat → IndexColType → Bool)
  (l1 : LocalContext)
  (target_goal_id : Nat)
  (modGoalIds modForwIds : IndexColType → m (IndexColType))
  (modGoalDirs modForwDirs : IndexColType → m IndexColType)
  (modGoalPI modLtxPI : PaInG IndexColType → LocalContext → LocalInstances → m (Prod3 (PaInG IndexColType) LocalContext LocalInstances))
  (modLocInst : LocalInstances → m LocalInstances)
  (IT : IntroTree IndexColType)
  : m (Prod (IntroTree IndexColType) LocalContext) :=
  let rec @[specialize] inner
    (seen : ListProd3 IndexColType IndexColType (IntroTree IndexColType)) :
    ListProd3 IndexColType IndexColType (IntroTree IndexColType) → (OptionProd3 IndexColType IndexColType (IntroTree IndexColType) × ListProd3 IndexColType IndexColType (IntroTree IndexColType))
    | .nil => (.none, seen)
    | .cons gods fods t more =>
        if contains target_goal_id gods
        then (.some gods fods t, seen.foldl more ListProd3.cons)
        else inner (.cons gods fods t seen) more
  let rec @[specialize] go
    (l2 : LocalInstances) (IT : IntroTree IndexColType)
    : m (Prod (IntroTree IndexColType) LocalContext) :=
      match IT with
      | .leaf ll2 goids foids goPI foPI => do
        let ⟨A,l1,_⟩ ← modGoalPI goPI l1 (l2 ++ ll2)
        let ⟨B,l1,_⟩ ← modLtxPI foPI l1 (l2 ++ ll2)
        return ⟨.leaf (← modLocInst ll2) (← modGoalIds goids) (← modForwIds foids) A B, l1⟩
      | .node ll2 goids foids goPI foPI kidsWdirs => do
          if contains target_goal_id goids
          then
            let ⟨A,l1,_⟩ ← modGoalPI goPI l1 (l2 ++ ll2)
            let ⟨B,l1,_⟩ ← modLtxPI foPI l1 (l2 ++ ll2)
            return ⟨.node (← modLocInst ll2) (← modGoalIds goids) (← modForwIds foids) A B kidsWdirs, l1⟩
          else
            let (loc,rest) := inner .nil kidsWdirs
            match loc with
            | .none => panic "[modGoalIdM] target {target_goal_id} not found among directions"
            | .some goIs foIs T => do
                let ⟨nT, l1⟩ ← go (l2 ++ ll2) T
                let nK := .cons (← modGoalDirs goIs) (← modForwDirs foIs) nT rest
                return ⟨.node ll2 goids foids goPI foPI  nK, l1⟩
  go #[] IT



@[specialize]
partial def modForwIdM {m} [Monad m]
  (contains : Nat → IndexColType → Bool)
  (l1 : LocalContext)
  (target_forw_id : Nat)
  (modGoalIds modForwIds : IndexColType → m IndexColType)
  (modGoalDirs modForwDirs : IndexColType → m IndexColType)
  (modGoalPI modLtxPI : PaInG IndexColType → LocalContext → LocalInstances → m (Prod3 (PaInG IndexColType) LocalContext LocalInstances))
  (modLocInst : LocalInstances → m LocalInstances)
  (IT : IntroTree IndexColType)
  : m (Prod (IntroTree IndexColType) LocalContext) :=
  let rec @[specialize] inner
    (seen : ListProd3 IndexColType IndexColType (IntroTree IndexColType)) :
    ListProd3 IndexColType IndexColType (IntroTree IndexColType) → (OptionProd3 IndexColType IndexColType (IntroTree IndexColType) × ListProd3 IndexColType IndexColType (IntroTree IndexColType))
    | .nil => (.none, seen)
    | .cons gods fods t more =>
        if contains target_forw_id fods
        then (.some gods fods t, seen.foldl more ListProd3.cons)
        else inner (.cons gods fods t seen) more
  let rec @[specialize] go
    (l2 : LocalInstances) (IT : IntroTree IndexColType)
    : m (Prod (IntroTree IndexColType) LocalContext) :=
    match IT with
    | .leaf ll2 goids foids goPI foPI => do
      let ⟨A,l1,_⟩ ← modGoalPI goPI l1 (l2 ++ ll2)
      let ⟨B,l1,_⟩ ← modLtxPI foPI l1 (l2 ++ ll2)
      return ⟨.leaf (← modLocInst ll2) (← modGoalIds goids) (← modForwIds foids) A B, l1⟩
    | .node ll2 goids foids goPI foPI kidsWdirs => do
        if contains target_forw_id foids
        then
          let ⟨A,l1,_⟩ ← modGoalPI goPI l1 (l2 ++ ll2)
          let ⟨B,l1,_⟩ ← modLtxPI foPI l1 (l2 ++ ll2)
          return ⟨.node (← modLocInst ll2) (← modGoalIds goids) (← modForwIds foids) A B kidsWdirs, l1⟩
        else
          let (loc,rest) := inner .nil kidsWdirs
          match loc with
          | .none => panic "[modGoalIdM] target {target_goal_id} not found among directions"
          | .some goIs foIs T => do
              let ⟨nT, l1⟩ ← go (l2 ++ ll2) T
              let nK := .cons (← modGoalDirs goIs) (← modForwDirs foIs) nT rest
              return ⟨.node ll2 goids foids goPI foPI  nK, l1⟩
  go #[] IT



-- # Specific


#check PaInG.insert

@[specialize]
def insertGoalsAtGoalId [Repr IndexColType]
  (contains : Nat → IndexColType → Bool)
  (union : IndexColType → IndexColType → IndexColType) (singleton : Nat → IndexColType)
  (emptyCol : IndexColType) (insert : Nat → IndexColType → IndexColType)
  (l1 : LocalContext)
  (target_goal_id : Nat) (IT : IntroTree IndexColType)
  (newGoals : ListProd Nat Expr)
  : MetaM (Prod (IntroTree IndexColType) LocalContext) :=
  let newGoalIds := newGoals.foldl emptyCol (fun x _ y => insert x y)
  IT.modGoalIdM contains l1 target_goal_id
    (fun x => return union newGoalIds x)
    (pure)
    (fun x => return union newGoalIds x)
    (pure)
    (fun goPI l1 l2 =>
      newGoals.foldlM ⟨goPI,l1,l2⟩ (fun i e ⟨T,l1,l2⟩ =>
        T.insert l1 l2 e i emptyCol singleton insert)
      )
    (fun x l1 l2 => return .mk x l1 l2)
    pure


/-- refer to version below-/
@[specialize]
def removeGoalId [Repr IndexColType]
  (contains : Nat → IndexColType → Bool)
  (erase : Nat → IndexColType → IndexColType)
  (difference : IndexColType → IndexColType → IndexColType) (singleton : Nat → IndexColType) (empty? : IndexColType → Bool)
  (emptyCol : IndexColType)
  (l1 : LocalContext)
  (target_goal_id : Nat) (IT : IntroTree IndexColType)
  : MetaM (Prod (IntroTree IndexColType) LocalContext) :=
  IT.modGoalIdM contains l1 target_goal_id
    (fun x => return erase target_goal_id x)
    (pure)
    (fun x => return erase target_goal_id x)
    (pure)
    (fun goPI l1 l2 =>
      let x := goPI.deleteOfInds (singleton target_goal_id) difference  emptyCol empty?
      return ⟨x,l1,l2⟩)
    (fun x l1 l2 => return ⟨x,l1,l2⟩)
    pure


/-- Should be used for unifications to get *active goals*.
Then, then IT still contains organisational information in its index fields,
and the PaIns can be used for unification ; though, the PaInG indices will only
be a subset of of those of the IT field
-/
@[specialize]
def removeGoalIdOnPaInOnly [Repr IndexColType]
  (contains : Nat → IndexColType → Bool)
  (difference : IndexColType → IndexColType → IndexColType) (singleton : Nat → IndexColType)
  (empty? : IndexColType → Bool) (emptyCol : IndexColType)
  (l1 : LocalContext)
  (target_goal_id : Nat) (IT : IntroTree IndexColType)
  : MetaM (Prod (IntroTree IndexColType) LocalContext) :=
  IT.modGoalIdM contains l1 target_goal_id
    pure
    (pure)
    pure
    (pure)
    (fun goPI l1 l2 =>
      let x := goPI.deleteOfInds (singleton target_goal_id) difference emptyCol empty?
      return ⟨x,l1,l2⟩)
    (fun x l1 l2 => return ⟨x,l1,l2⟩)
    pure




@[specialize]
def insertForwsAtGoalId [Repr IndexColType]
  (contains : Nat → IndexColType → Bool)
  (union : IndexColType → IndexColType → IndexColType) (singleton : Nat → IndexColType)
  (emptyCol : IndexColType) (insert : Nat → IndexColType → IndexColType)
  (l1 : LocalContext)
  (target_goal_id : Nat) (IT : IntroTree IndexColType)
  (newForws : ListProd Nat Expr)
  : MetaM (Prod (IntroTree IndexColType) LocalContext) :=
  let newGoalIds := newForws.foldl emptyCol (fun x _ y => insert x y)
  IT.modGoalIdM contains l1 target_goal_id
    (pure)
    (fun x => return union newGoalIds x)
    (pure)
    (fun x => return union newGoalIds x)
    (fun x l1 l2 => return ⟨x,l1,l2⟩)
    (fun goPI l1 l2 =>
      newForws.foldlM ⟨goPI,l1,l2⟩ (fun i e ⟨T,l1,l2⟩ =>
        T.insert l1 l2 e i emptyCol singleton insert)
      )
    pure


@[specialize]
partial def gatherUGidsToGoalId
  (contains : Nat → IndexColType → Bool)
  (union : IndexColType → IndexColType → IndexColType)
  (target_goal_id : Nat)
  (ini : IndexColType)
  (IT : IntroTree IndexColType)
  : IndexColType :=
  let rec @[specialize] inner :
    ListProd3 IndexColType IndexColType (IntroTree IndexColType) → (OptionProd3 IndexColType IndexColType (IntroTree IndexColType))
    | .nil => (.none)
    | .cons gods fods t more =>
        if contains target_goal_id gods
        then (.some gods fods t)
        else inner more
  match IT with
  | .leaf _ _ foids _ _ =>
      union foids ini
  | .node _ goids foids _ _ kidsWdirs =>
      if contains target_goal_id goids
      then
        union foids ini
      else
        match inner kidsWdirs with
        | .none => panic s!"[gatherUGidsToGoalId] target {target_goal_id} not found among directions"
        | .some _ _ T =>
            gatherUGidsToGoalId contains union target_goal_id (union foids ini) T



@[specialize]
partial def gatherUGidsAtGoalId
  (contains : Nat → IndexColType → Bool)
  (union : IndexColType → IndexColType → IndexColType)
  (target_goal_id : Nat)
  (IT : IntroTree IndexColType)
  : IndexColType :=
  let rec @[specialize] inner :
    ListProd3 (IndexColType) (IndexColType) (IntroTree (IndexColType)) → (OptionProd3 (IndexColType) (IndexColType) (IntroTree (IndexColType)))
    | .nil => (.none)
    | .cons gods fods t more =>
        if contains target_goal_id gods
        then (.some gods fods t)
        else inner more
  match IT with
  | .leaf _ _ foids _ _ => foids
  | .node _ goids foids _ _ kidsWdirs =>
      if contains target_goal_id goids
      then
        foids
      else
        match inner kidsWdirs with
        | .none => panic s!"[gatherUGidsToGoalId] target {target_goal_id} not found among directions"
        | .some _ _ T =>
            gatherUGidsAtGoalId contains union target_goal_id T



@[specialize]
partial def gatherUGidsToGoalIdStrict
  (contains : Nat → IndexColType → Bool)
  (union : IndexColType → IndexColType → IndexColType)
  (target_goal_id : Nat)
  (ini : IndexColType)
  (IT : IntroTree (IndexColType))
  : IndexColType :=
  trace set TracingFlags.none in
  trace on .zero with s!"[gatherUGidsToGoalIdStrict] call on ini {ini} IT {IT.pp 0}" in
  let rec @[specialize] inner :
    ListProd3 (IndexColType) (IndexColType) (IntroTree (IndexColType)) → (OptionProd3 (IndexColType) (IndexColType) (IntroTree (IndexColType)))
    | .nil => (.none)
    | .cons gods fods t more =>
        if contains target_goal_id gods
        then (.some gods fods t)
        else inner more
  match IT with
  | .leaf _ _ _ _ _ => ini
  | .node _ goids foids _ _ kidsWdirs =>
      if contains target_goal_id goids
      then
        ini
      else
        match inner kidsWdirs with
        | .none => panic s!"[gatherUGidsToGoalId] target {target_goal_id} not found among directions"
        | .some _ _ T =>
            gatherUGidsToGoalIdStrict contains union target_goal_id (union foids ini) T



@[specialize]
partial def integrateIntro
  [Repr IndexColType]
  (union : IndexColType → IndexColType → IndexColType)
  (contains : Nat → IndexColType → Bool) (singleton : Nat → IndexColType)
  (emptyCol : IndexColType) (insert : Nat → IndexColType → IndexColType)
  (l1 : LocalContext)
  (spawn_goal_id : Nat) (IT : IntroTree IndexColType) (head_goal_id : Nat) (head_goal : Expr) (newIntroForw : ListProd3 Nat FVarId Expr)
  : MetaM (Prod (IntroTree IndexColType) LocalContext) :=
  let rec @[specialize] inner
    (seen : ListProd3 IndexColType IndexColType (IntroTree IndexColType)) :
    ListProd3 IndexColType IndexColType (IntroTree IndexColType) → (OptionProd3 IndexColType IndexColType (IntroTree IndexColType) × ListProd3 IndexColType IndexColType (IntroTree IndexColType))
    | .nil => (.none, seen)
    | .cons gods fods t more =>
        if contains spawn_goal_id gods
        then (.some gods fods t, seen.foldl more ListProd3.cons)
        else inner (.cons gods fods t seen) more
  let rec @[specialize] go (l2 : LocalInstances)
    (newFids : IndexColType) (head_goal_idx : IndexColType)
    (IT : IntroTree IndexColType) : MetaM (Prod (IntroTree IndexColType) LocalContext) :=
    match IT with
    | .leaf ll2 goids foids goPI foPI => do
      -- let ngoI := goids.orderedInsertOrLeave head_goal_id
      -- let nfoI := List.orderedUnion foids newFids
      let il2 := l2 ++ ll2
      let nl2 : LocalInstances := ← newIntroForw.foldlM #[] (fun _ fv T L2 => do
        match ← IsClass? T l1 il2 with
        | .none => return L2
        | .some cn => return L2.push (.mk cn (.fvar fv))
        )
      let fl2 := (il2 ++ nl2)
      let ⟨nG,l1,_⟩ ← PaInG.dead.insert l1 fl2 head_goal head_goal_id emptyCol singleton insert
      let ⟨nT,l1,_⟩ ← newIntroForw.foldlM (⟨PaInG.dead,l1,fl2⟩ : Prod3 _ _ _) (fun i _ e (.mk R l1 l2) => do
        R.insert l1 l2 e i emptyCol singleton insert
        )
      return ⟨.node ll2 goids foids goPI foPI (.cons head_goal_idx newFids (.leaf nl2 (singleton head_goal_id) newFids nG nT) .nil), l1 ⟩
    | .node ll2 goids foids goPI foPI kidsWdirs => do
        if contains spawn_goal_id goids
        then
          -- let ngoI := goids.orderedInsertOrLeave head_goal_id
          -- let nfoI := List.orderedUnion foids newFids
          let il2 := l2 ++ ll2
          let nl2 : LocalInstances := ← newIntroForw.foldlM #[] (fun _ fv T L2 => do
            match ← IsClass? T l1 il2 with
            | .none => return L2
            | .some cn => return L2.push (.mk cn (.fvar fv))
            )
          let fl2 := (il2 ++ nl2)
          let ⟨nG,l1,_⟩ ← PaInG.dead.insert l1 fl2 head_goal head_goal_id emptyCol singleton insert
          let ⟨nT,l1,_⟩ ← newIntroForw.foldlM (⟨PaInG.dead,l1,fl2⟩ : Prod3 _ _ _) (fun i _ e (.mk R l1 l2) => do
            R.insert l1 l2 e i emptyCol singleton insert
            )
          return ⟨.node ll2 goids foids goPI foPI (.cons head_goal_idx newFids (.leaf nl2 (singleton head_goal_id) newFids nG nT) kidsWdirs), l1⟩
        else
          let (loc,rest) := inner .nil kidsWdirs
          match loc with
          | .none => panic s!"[integrateIntro] target {spawn_goal_id} not found among directions"
          | .some goIs foIs T => do
              let .mk nT l1 ← go (l2 ++ ll2) newFids head_goal_idx T
              -- let ngoI := goids.orderedInsertOrLeave head_goal_id
              -- let nfoI := List.orderedUnion foids newFids
              let ngoID := insert head_goal_id goIs
              let nfoID := union foIs newFids
              let nK := .cons ngoID nfoID nT rest
              return ⟨.node ll2 goids foids goPI foPI  nK, l1⟩
  do
  let newFids := newIntroForw.foldl emptyCol (fun n _ _ r => insert n r)
  let head_goal_idx := singleton head_goal_id
  go #[] newFids head_goal_idx IT



/-- Assumes `target_forw_ids` is consistent, ie. are on a same path on the introtree-/
@[specialize]
partial def insertForwAtForwIds [Repr IndexColType]
  (contains : Nat → IndexColType → Bool)
  (diff: IndexColType → IndexColType → IndexColType) (singleton : Nat → IndexColType)
  (emptyCol : IndexColType) (insert : Nat → IndexColType → IndexColType) (empty? : IndexColType → Bool)
  (head : IndexColType → Nat)
  (l1 : LocalContext)
  (target_forw_ids : IndexColType) (IT : IntroTree IndexColType)
  (new_forw_id : Nat) (new_forw_type : Expr) (new_forw_fv : FVarId)
  : MetaM (Prod (IntroTree IndexColType) LocalContext) :=
    -- let target_forw_ids := target_forw_ids.mergeSort
    let rec @[specialize] inner (dir : Nat)
      (seen : ListProd3 IndexColType IndexColType (IntroTree IndexColType)) :
      ListProd3 IndexColType IndexColType (IntroTree IndexColType) → (OptionProd3 IndexColType IndexColType (IntroTree IndexColType) × ListProd3 IndexColType IndexColType (IntroTree IndexColType))
      | .nil => (.none, seen)
      | .cons gods fods t more =>
          if contains dir fods
          then (.some gods fods t, seen.foldl more ListProd3.cons)
          else inner dir (.cons gods fods t seen) more
    let rec @[specialize] go
      (l2 : LocalInstances) (target_forw_ids : IndexColType) (IT : IntroTree IndexColType) :=
      match IT with
      | .leaf ll2 goids foids goPI foPI => do
          let D := diff target_forw_ids foids
          if empty? D
          then
            let fl2 := l2 ++ ll2
            let ⟨nF,l1,_⟩ ← foPI.insert l1 fl2 new_forw_type new_forw_id emptyCol singleton insert
            let nl2 : LocalInstances := ← (do
              match ← IsClass? new_forw_type l1 fl2 with
              | .none => return ll2
              | .some cn => return ll2.push (.mk cn (.fvar new_forw_fv))
              )
            return ⟨.leaf nl2 goids (insert new_forw_id foids) goPI nF,l1⟩
          else
            throwError s!"[insertForwAtForwIds] reached leaf but {repr D} remains"
      | .node ll2 goids foids goPI foPI kids => do
          let D := diff target_forw_ids foids
          if empty? D
          then
            let fl2 := l2 ++ ll2
            let ⟨nF,l1,_⟩ ← foPI.insert l1 fl2 new_forw_type new_forw_id emptyCol singleton insert
            let nl2 : LocalInstances := ← (do
              match ← IsClass? new_forw_type l1 fl2 with
              | .none => return ll2
              | .some cn => return ll2.push (.mk cn (.fvar new_forw_fv))
              )
            return ⟨.node nl2 goids (insert new_forw_id foids) goPI nF kids,l1⟩
          else
            let nx := head D
              let (found,rest) := inner nx .nil kids
              match found with
              | .none => throwError s!"[insertForwAtForwIds] searching for {repr D}, but not found in directions"
              | .some gods fods t =>
                  let ⟨nt,l1⟩ ← go l2 D t
                  let nfods := insert new_forw_id fods
                  -- return ⟨.node goids (foids.orderedInsertOrLeave new_forw_id) goPI foPI (.cons gods nfods nt rest),l1,l2⟩
                  return ⟨.node ll2 goids foids goPI foPI (.cons gods nfods nt rest),l1⟩
  go #[] target_forw_ids IT


-- # Other

/-- TODO: version that asks about partiular branch of introtree-/
@[specialize]
partial def hasForw? [Repr IndexColType]
  (empty? : IndexColType → Bool)
  (intersect union : IndexColType → IndexColType → IndexColType) (empty : IndexColType) (revCountMax : Nat)
  (l1 : LocalContext)
  (ce : Expr) (T : IntroTree IndexColType)
  : MetaM (Prod Bool LocalContext) :=
  let rec @[specialize] go (l1 : LocalContext) : ListProd LocalInstances (IntroTree IndexColType) → MetaM (Prod Bool LocalContext)
    | .nil => return ⟨false,l1⟩
    | .cons l2 nx more =>
        match nx with
        | .leaf ll2 _ is _ ltx => do
            let nl2 := l2 ++ ll2
            let ⟨qase,_,_,l1,_⟩ ← ltx.findCore l1 nl2
              empty? intersect union empty is revCountMax
              ce
            if qase == 3
            then return ⟨true,l1⟩
            else go l1 more
        | .node ll2 _ is _ ltx kidsWdirs => do
            let nl2 := l2 ++ ll2
            let ⟨qase,_,_,l1,_⟩ ← ltx.findCore l1 nl2
              empty? intersect union empty is revCountMax
              ce
            if qase == 3
            then return ⟨true,l1⟩
            else go l1 (kidsWdirs.foldl more (fun _ _ it m => .cons nl2 it m))
  go l1 (.cons #[] T .nil)




@[specialize]
partial def hasForwAtGoalId? [Repr IndexColType]
  (target_goal_id : Nat)
  (contains : Nat → IndexColType → Bool) (empty? : IndexColType → Bool)
  (intersect union : IndexColType → IndexColType → IndexColType) (empty : IndexColType) (revCountMax : Nat)
  (l1 : LocalContext)
  (ce : Expr) (T : IntroTree IndexColType)
  : MetaM (Prod Bool LocalContext) :=
  let rec @[specialize] inner :
    ListProd3 IndexColType IndexColType (IntroTree IndexColType) → (Option (IntroTree IndexColType))
    | .nil => (.none)
    | .cons gods _ t more =>
        if contains target_goal_id gods
        then (.some t)
        else inner more
  let rec @[specialize] go (l1 : LocalContext) (l2 : LocalInstances) : (IntroTree IndexColType) → MetaM (Prod Bool LocalContext)
    | .leaf ll2 _ is _ ltx => do
        let ⟨qase,_,_,l1,_⟩ ← ltx.findCore l1 (l2 ++ ll2)
          empty? intersect union empty is revCountMax
          ce
        if qase == 3
        then return ⟨true,l1⟩
        else return ⟨false,l1⟩
    | .node ll2 _ is _ ltx kidsWdirs => do
        let nl2 := (l2 ++ ll2)
        let ⟨qase,_,_,l1,_⟩ ← ltx.findCore l1 nl2
          empty? intersect union empty is revCountMax
          ce
        if qase == 3
        then return ⟨true,l1⟩
        else
          let nx :=
              match inner kidsWdirs with
              | .some x => x
              | .none => panic s!"[hasForwAtGoalId?] goal {target_goal_id} is not among kidsWdirs"
          go l1 nl2 nx
  go l1 #[] T



/-- Assumes `target_forw_ids` is consistent, ie. are on a same path on the introtree-/
@[specialize]
partial def hasForwEAtForwIds? [Repr IndexColType]
  (empty? : IndexColType → Bool)
  (intersect union diff : IndexColType → IndexColType → IndexColType) (empty : IndexColType) (revCountMax : Nat)
  (l1 : LocalContext)
  (target_forw_ids : IndexColType) (ce : Expr) (IT : IntroTree IndexColType)
  : MetaM (Prod3 Bool LocalContext LocalInstances) :=
  -- let target_forw_ids := target_forw_ids.mergeSort
  let rec @[specialize] inner (target_forw_ids : IndexColType) :
    ListProd3 IndexColType IndexColType (IntroTree IndexColType) → (Option (IntroTree IndexColType))
    | .nil => (.none)
    | .cons _ foIds t more =>
        if empty? (diff target_forw_ids foIds)
        then
          (.some t)
        else
          inner target_forw_ids more
  let rec @[specialize] go (l1 : LocalContext) (l2 : LocalInstances) (target_forw_ids : IndexColType) : (IntroTree IndexColType) → MetaM (Prod3 Bool LocalContext LocalInstances)
    | .leaf ll2 _ is _ ltx => do
        let nl2 := (l2 ++ ll2)
        let ⟨qase,_,_,l1,_⟩ ← ltx.findCore l1 nl2
          empty? intersect union empty is revCountMax
          ce
        if qase == 3
        then return ⟨true,l1,l2⟩
        else return ⟨false,l1,l2⟩
    | .node ll2 _ is _ ltx kidsWdirs => do
        let nl2 := (l2 ++ ll2)
        let ⟨qase,_,_,l1,_⟩ ← ltx.findCore l1 nl2
          empty? intersect union empty is revCountMax
          ce
        if qase == 3
        then return ⟨true,l1,l2⟩
        else
          let nx := (diff target_forw_ids is)
          if empty? nx
          then return ⟨false,l1,l2⟩
          else
            match inner nx kidsWdirs with
            | .some x => go l1 l2 nx x
            | .none => panic s!"[hasForwEAtForwIds?] forws {repr nx} is not among kidsWdirs"
  go l1 #[] target_forw_ids IT




/-- Assumes `target_forw_ids` is consistent, ie. are on a same path on the introtree-/
@[specialize]
partial def forwCoherent? [Repr IndexColType]
  (empty? : IndexColType → Bool)
  (contains : Nat → IndexColType → Bool)
  (diff : IndexColType → IndexColType → IndexColType)
  (target_forw_ids : IndexColType) (forwI : Nat) (IT : IntroTree IndexColType)
  : Bool :=
  -- let target_forw_ids := target_forw_ids.mergeSort
  let rec @[specialize] inner (target_forw_ids : IndexColType) :
    ListProd3 IndexColType IndexColType (IntroTree IndexColType) → (Option (IntroTree IndexColType))
    | .nil => (.none)
    | .cons _ foIds t more =>
        if empty? (diff target_forw_ids foIds)
        then
          (.some t)
        else
          inner target_forw_ids more
  let rec @[specialize] go (target_forw_ids : IndexColType) : (IntroTree IndexColType) → Bool
    | .leaf _ _ is _ _ => contains forwI is
    | .node _ _ is _ _ kidsWdirs =>
        if contains forwI is
        then true
        else
          let nx := (diff target_forw_ids is)
          if empty? nx
          then false
          else
            match inner nx kidsWdirs with
            | .some x => go nx x
            | .none => panic s!"[forwCoherent?] forws {repr nx} is not among kidsWdirs"
  go target_forw_ids IT


/-- Assumes `target_forw_ids` is consistent, ie. are on a same path on the introtree-/
@[specialize]
partial def forwGoalCoherent? [Repr IndexColType]
  (empty? : IndexColType → Bool)
  (contains : Nat → IndexColType → Bool)
  (diff : IndexColType → IndexColType → IndexColType)
  (target_forw_ids : IndexColType) (goalI : Nat) (IT : IntroTree IndexColType)
  : Bool :=
  -- let target_forw_ids := target_forw_ids.mergeSort
  let rec @[specialize] inner (target_forw_ids : IndexColType) :
    ListProd3 IndexColType IndexColType (IntroTree IndexColType) → (Option (IntroTree IndexColType))
    | .nil => (.none)
    | .cons _ foIds t more =>
        if empty? (diff target_forw_ids foIds)
        then
          (.some t)
        else
          inner target_forw_ids more
  let rec @[specialize] go (target_forw_ids : IndexColType) : (IntroTree IndexColType) → Bool
    | .leaf _ is _ _ _ => contains goalI is
    | .node _ is Is _ _ kidsWdirs =>
        if contains goalI is
        then true
        else
          let nx := (diff target_forw_ids Is)
          if empty? nx
          then false
          else
            match inner nx kidsWdirs with
            | .some x => go nx x
            | .none => panic s!"[forwGoalCoherent?] forws {repr nx} is not among kidsWdirs"
  go target_forw_ids IT



@[specialize]
partial def hasGoal? [Repr IndexColType]
  (empty? : IndexColType → Bool)
  (intersect union : IndexColType → IndexColType → IndexColType) (empty : IndexColType) (revCountMax : Nat)
  (l1 : LocalContext)
  (ce : Expr) (T : IntroTree IndexColType) : MetaM (Prod Bool LocalContext) :=
  let rec @[specialize] go (l1 : LocalContext)
    : ListProd LocalInstances (IntroTree IndexColType) → MetaM (Prod Bool LocalContext)
    | .nil => return ⟨false,l1⟩
    | .cons l2 nx more =>
        match nx with
        | .leaf ll2 is _ _ ltx => do
            let nl2 := (l2 ++ ll2)
            let ⟨qase,_,_,l1,_⟩ ← ltx.findCore l1 nl2
              empty? intersect union empty is revCountMax
              ce
            if qase == 3
            then return ⟨true,l1⟩
            else go l1 more
        | .node ll2 is _ _ ltx kidsWdirs => do
            let nl2 := (l2 ++ ll2)
            let ⟨qase,_,_,l1,_⟩ ← ltx.findCore l1 nl2
              empty? intersect union empty is revCountMax
              ce
            if qase == 3
            then return ⟨true,l1⟩
            else go l1 (kidsWdirs.foldl more (fun _ _ it m => .cons nl2 it m))
  go l1 (.cons #[] T .nil)




-- somehow the right one for assembly
@[specialize]
partial def mergeLtxForGoalId {m} [Monad m] [Repr IndexColType]
  (contains : Nat → IndexColType → Bool)
  (union : IndexColType → IndexColType → IndexColType) (emptyCol : IndexColType)
  (target_goal_id : Nat)
  (IT : IntroTree IndexColType)
  (init : PaInG IndexColType)
  : m (PaInG IndexColType) :=
  let rec @[specialize] inner :
    ListProd3 IndexColType IndexColType (IntroTree IndexColType) → (OptionProd3 IndexColType IndexColType (IntroTree IndexColType))
    | .nil => (.none)
    | .cons gods fods t more =>
        if contains target_goal_id gods
        then (.some gods fods t)
        else inner more
  match IT with
  | .leaf _ _ _ _ foPI => do
      return PaInG.merge union emptyCol foPI init
  | .node _ goids _ _ foPI kidsWdirs => do
      if contains target_goal_id goids
      then
        return PaInG.merge union emptyCol foPI init
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
  (init : PaInG IndexColType)
  : m (PaInG IndexColType) :=
  let rec @[specialize] inner :
    ListProd3 IndexColType IndexColType (IntroTree IndexColType) → (OptionProd3 IndexColType IndexColType (IntroTree IndexColType))
    | .nil => (.none)
    | .cons gods fods t more =>
        if contains target_goal_id gods
        then (.some gods fods t)
        else inner more
  match IT with
  | .leaf _ _ _ _ foPI => do
      return PaInG.merge union emptyCol foPI init
  | .node _ goids _ _ foPI kidsWdirs => do
      if contains target_goal_id goids
      then
        return PaInG.merge union emptyCol foPI init
      else
        match inner kidsWdirs with
        | .none => return panic s!"[mergeLtxForGoalIdTruely] target {target_goal_id} not found among directions"
        | .some _ _ T => do
            mergeLtxForGoalIdTruely
              contains union emptyCol target_goal_id T (PaInG.merge union emptyCol foPI init)



@[specialize]
partial def mergeLtxForForwIds {m} [Monad m] [Repr IndexColType]
  (empty? : IndexColType → Bool)
  (union diff : IndexColType → IndexColType → IndexColType) (emptyCol : IndexColType)
  (target_forw_ids : IndexColType)
  (IT : IntroTree IndexColType)
  (init : PaInG IndexColType)
  : m (PaInG IndexColType) :=
  -- let target_forw_ids := target_forw_ids.mergeSort
  let rec @[specialize] inner (target_forw_ids : IndexColType) :
    ListProd3 IndexColType IndexColType (IntroTree IndexColType) → (Option (IntroTree IndexColType))
    | .nil => (.none)
    | .cons _ foIds t more =>
        if empty? (diff target_forw_ids foIds)
        then
          (.some t)
        else
          inner target_forw_ids more
  match IT with
  | .leaf _ _ _ _ foPI => do
      return PaInG.merge union emptyCol foPI init
  | .node _ _ foIds _ foPI kidsWdirs => do
      let nx := (diff target_forw_ids foIds)
      if empty? nx
      then
        return PaInG.merge union emptyCol foPI init
      else
        match inner nx kidsWdirs with
        | .none => return panic s!"[mergeLtxForForwIds] target {repr target_forw_ids} not found among directions"
        | .some T => mergeLtxForForwIds empty? union diff emptyCol target_forw_ids T init



@[specialize]
partial def mergeGoalsForForwId [Repr IndexColType]
  (contains : Nat → IndexColType → Bool)
  (union : IndexColType → IndexColType → IndexColType) (emptyCol : IndexColType)
  (target_gu_id : Nat)
  (IT : IntroTree IndexColType)
  : PaInG IndexColType :=
  let rec @[specialize] inner :
    ListProd3 IndexColType IndexColType (IntroTree IndexColType) → (Option (IntroTree IndexColType))
    | .nil => (.none)
    | .cons _ fods t more =>
        if contains target_gu_id fods
        then (.some t)
        else inner more
  let rec @[specialize] locate : IntroTree IndexColType → IntroTree IndexColType
    | x@(.leaf ..) => x
    | x@(.node _ _ foIds _ _ kidsWdirs) =>
        if contains target_gu_id foIds
        then x
        else
          match inner kidsWdirs with
          | .none => panic s!"[mergeGoalsForForwId] target {target_gu_id} not found among directions"
          | .some T => locate T
  let subIT := locate IT
  let rec go (t : PaInG IndexColType) : List (IntroTree IndexColType) → PaInG IndexColType
    | [] => t
    | .leaf _ _ _ gs _ :: more => go (PaInG.merge union emptyCol gs t) more
    | .node _ _ _ gs _ kids :: more => go (PaInG.merge union emptyCol gs t) (kids.foldl more (fun _ _ k R => k :: R))
  go .dead [subIT]



@[specialize]
partial def mergeGoalsForForwIds [Repr IndexColType]
  (empty? : IndexColType → Bool)
  (union diff : IndexColType → IndexColType → IndexColType) (emptyCol : IndexColType)
  (target_forw_ids : IndexColType)
  (IT : IntroTree IndexColType)
  : PaInG IndexColType :=
  -- let target_forw_ids := target_forw_ids.mergeSort
  let rec @[specialize] inner (target_forw_ids : IndexColType) :
    ListProd3 IndexColType IndexColType (IntroTree IndexColType) → (Option (IntroTree IndexColType))
    | .nil => (.none)
    | .cons _ foIds t more =>
        if empty? (diff target_forw_ids foIds)
        then
          (.some t)
        else
          inner target_forw_ids more
  let rec @[specialize] locate (target_forw_ids : IndexColType) : IntroTree IndexColType → IntroTree IndexColType
    | x@(.leaf ..) => x
    | x@(.node _ _ foIds _ _ kidsWdirs) =>
        let nx := (diff target_forw_ids foIds)
        if empty? nx
        then x
        else
          match inner nx kidsWdirs with
          | .none => panic s!"[mergeGoalsForForwIds] target {repr target_forw_ids} not found among directions"
          | .some T => locate nx T
  let subIT := locate target_forw_ids IT
  let rec go (t : PaInG IndexColType) : List (IntroTree IndexColType) → PaInG IndexColType
    | [] => t
    | .leaf _ _ _ gs _ :: more => go (PaInG.merge union emptyCol gs t) more
    | .node _ _ _ gs _ kids :: more => go (PaInG.merge union emptyCol gs t) (kids.foldl more (fun _ _ k R => k :: R))
  go .dead [subIT]


/-- Assumes `target_forw_ids` is consistent, ie. are on a same path on the introtree-/
@[specialize]
partial def forwIdsFromforwId [Repr IndexColType]
  (empty? : IndexColType → Bool)
  (union diff : IndexColType → IndexColType → IndexColType) (emptyCol : IndexColType)
  (target_forw_ids : IndexColType)
  (IT : IntroTree (IndexColType))
  : IndexColType :=
  -- let target_forw_ids := target_forw_ids.mergeSort
  let rec inner (target_forw_ids : IndexColType) :
    ListProd3 (IndexColType) (IndexColType) (IntroTree (IndexColType)) → (Option (IntroTree (IndexColType)))
    | .nil => (.none)
    | .cons _ fods t more =>
        -- dbg_trace s!"[forwIdsFromforwId] fods {fods}"
        if empty? (diff target_forw_ids fods)
        then (.some t)
        else inner target_forw_ids more
  let rec locate (target_forw_ids : IndexColType) (done : IndexColType) : IntroTree (IndexColType) → (IndexColType × IntroTree (IndexColType))
    | x@(.leaf ..) => (done, x)
    | x@(.node _ _ foIds _ _ kidsWdirs) =>
        -- dbg_trace s!"[forwIdsFromforwId] target_forw_ids {target_forw_ids} foIds {foIds}"
        let next := (diff target_forw_ids foIds)
        -- dbg_trace s!"[forwIdsFromforwId] next {next}"
        if empty? next
        then (done, x)
        else
          match inner next kidsWdirs with
          | .none => panic s!"[forwIdsFromforwId] target {repr target_forw_ids} not found among directions"
          | .some T => locate next (union foIds done) T
  let (fromRoot,subIT) := locate target_forw_ids emptyCol IT
  let rec go (done : IndexColType) : List (IntroTree (IndexColType)) → (IndexColType)
    | [] => done
    | .leaf _ _ fo _ _ :: more => go (union fo done) more
    | .node _ _ fo _ _ kids :: more => go (union fo done) (kids.foldl more (fun _ _ k R => k :: R))
  go fromRoot [subIT]



@[specialize]
partial def topGoalForForwId [Repr IndexColType]
  (contains : Nat → IndexColType → Bool) (empty? : IndexColType → Bool)
  (intersect : IndexColType → IndexColType → IndexColType)
  (singleton : Nat → IndexColType) (head : IndexColType → Nat)
  (l1 : LocalContext) (target_forw_id : Nat)
  (IT : IntroTree (IndexColType))
  : MetaM (Prod3 Nat Expr LocalContext) :=
  let rec inner :
    ListProd3 (IndexColType) (IndexColType) (IntroTree (IndexColType)) → (Option (IntroTree (IndexColType)))
    | .nil => (.none)
    | .cons _ fods t more =>
        if (contains target_forw_id fods)
        then (.some t)
        else inner  more
  let rec go (l2 : LocalInstances) : IntroTree (IndexColType) → MetaM (Prod3 Nat Expr LocalContext)
    | .leaf ll2 goi fo goalPI _  => do
        if contains target_forw_id fo
        then
          if empty? goi
          then panic s!"[topGoalForForwId] goal indices are empty !"
          else
            let h' := head goi
            let h := singleton h'
            let terms ← goalPI.buildCore l1 (l2 ++ ll2) [] 0 (fun x => intersect x h) intersect empty?
            match terms with
            | .nil => panic s!"[topGoalForForwId] goal {h'} isn't contained in path index of goals ..."
            | .cons e _ _ => return .mk h' e l1
        else
          panic s!"[topGoalForForwId] arrived at leaf but didin't find forw id {target_forw_id}"
    | .node ll2 goi fo goalPI _ kids => do
        if contains target_forw_id fo
        then
          if empty? goi
          then panic s!"[topGoalForForwId] goal indices are empty !"
          else
            let h' := head goi
            let h := singleton h'
            let terms ← goalPI.buildCore l1 (l2 ++ ll2) [] 0 (fun x => intersect x h) intersect empty?
            match terms with
            | .nil => panic s!"[topGoalForForwId] goal {h'} isn't contained in path index of goals ..."
            | .cons e _ _ => return .mk h' e l1
        else
          match inner kids with
          | .none => panic s!"[topGoalForForwId] didn't find forw id {target_forw_id} in kids of node"
          | .some t => go (l2 ++ ll2) t
  go #[] IT



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
    | .leaf _ _ is _ _ =>
        contains target_forw_id is
    | .node _ _ is _ _ kidsWdirs =>
        if contains target_forw_id is
        then  true
        else
          match inner kidsWdirs with
          | .none => false --panic s!"[hasForwIdAtGoalId?] didn find {target_goal_id} among kids"
          | .some t => go t
  go T


partial def getGoalOfGoalId
  (contains : Nat → IndexColType → Bool) (empty? : IndexColType → Bool)
  (intersect : IndexColType → IndexColType → IndexColType)
  (singleton : Nat → IndexColType)
  (l1 : LocalContext) (target_goal_id : Nat)
  (T : IntroTree (IndexColType)) : MetaM Expr :=
  let rec inner :
    ListProd3 (IndexColType) (IndexColType) (IntroTree (IndexColType)) → (Option (IntroTree (IndexColType)))
    | .nil => (.none)
    | .cons gods _ t more =>
        if contains target_goal_id gods
        then (.some t)
        else inner more
  let rec go (l2 : LocalInstances) : (IntroTree (IndexColType)) → MetaM Expr
    | .leaf ll2 _ _ gs _ => do
        let h := singleton target_goal_id
        let terms ← gs.buildCore l1 (l2 ++ ll2) [] 0 (fun x => intersect x h) intersect empty?
        match terms with
        | .cons e _ _ => return e
        | _ => panic s!"[getGoalOfGoalId] build of {target_goal_id} failed"
    | .node ll2 is _ gs _ kidsWdirs => do
        if contains target_goal_id is
        then
          let h := singleton target_goal_id
          let terms ← gs.buildCore l1 (l2 ++ ll2) [] 0 (fun x => intersect x h) intersect empty?
          match terms with
          | .cons e _ _ => return e
          | _ => panic s!"[getGoalOfGoalId] build of {target_goal_id} failed"
        else
          match inner kidsWdirs with
          | .none => panic s!"[getGoalOfGoalId] didn find {target_goal_id} among kids"
          | .some t => go (l2 ++ ll2) t
  go #[] T
