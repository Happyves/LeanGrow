
/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Caching.Score.SampleClassify


open Lean Meta


@[specialize]
def generalize_back_cvbThm_core
  {IdxCollType : Type} [Repr IdxCollType]
  (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β) (empty : IdxCollType)
  (insert : Nat → IdxCollType → IdxCollType)
  (insertMulti intersect union difference : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (size : IdxCollType → Nat) (contains : Nat → IdxCollType → Bool)
  (genCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (commonType : Expr) → (branchDepth : Nat) → Bool)
  (freqCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (branchDepth : Nat) → Bool)
  (init : ProcessedSamplesThmKey IdxCollType)
  : MetaM (scoreThmKey IdxCollType) := do
  let .mk (_,cleanTypes) resRegB ← cvb_thms_genMain
    fold empty insert insertMulti intersect union difference
    empty? size contains (← getLCtx) (← getLocalInstances)
    genCondition freqCondition
    init.sampleName init.types #[] init.regularBack
  let .mk (_,cleanTypes) resRegF ← cvb_thms_genMain
    fold empty insert insertMulti intersect union difference
    empty? size contains (← getLCtx) (← getLocalInstances)
    genCondition freqCondition
    init.sampleName init.types cleanTypes init.regularForw
  let ((_,cleanTypes), subP) ← cvb_thms_genMain_subPat --.mk sT W tw _ cleanTypes
    fold empty insert insertMulti intersect union difference
    empty? size contains  (← getLCtx) (← getLocalInstances)
    genCondition freqCondition
    init.sampleName init.types cleanTypes init.subpat
  let .mk (_,cleanTypes) resConj ← cvb_thmConj_genMain
    fold empty insert insertMulti intersect union difference
    empty? size contains (← getLCtx) (← getLocalInstances)
    genCondition freqCondition
    init.sampleName init.types cleanTypes init.conj
  return .mk init.sampleName resRegB resRegF subP resConj init.levelNum cleanTypes

#check 1



@[specialize]
def generalize_back_cvbGoalHyp_core
  {IdxCollType : Type} [Repr IdxCollType]
  (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β) (empty : IdxCollType)
  (insert : Nat → IdxCollType → IdxCollType)
  (insertMulti intersect union difference : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (size : IdxCollType → Nat) (contains : Nat → IdxCollType → Bool)
  (shiftAdd : IdxCollType → Nat → IdxCollType)
  (genCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (commonType : Expr) → (branchDepth : Nat) → Bool)
  (freqCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (branchDepth : Nat) → Bool)
  (init : ProcessedSamplesGHKey IdxCollType)
  : MetaM (scoreGHKey IdxCollType) := do
  let .mk _ cleanTypes resRegB ← cvb_goal_hyp_genMain
    fold empty shiftAdd insert insertMulti intersect union difference
    empty? size contains (← getLCtx) (← getLocalInstances) genCondition freqCondition
    init.sampleName init.types #[] init.regularBack
  let .mk _ cleanTypes resRegF ← cvb_goal_hyp_genMain
    fold empty shiftAdd insert insertMulti intersect union difference
    empty? size contains (← getLCtx) (← getLocalInstances) genCondition freqCondition
    init.sampleName init.types cleanTypes init.regularForw
  let .mk sT W tw _ cleanTypes ← cvb_goal_hyp_genMain_subPat
    fold empty insert insertMulti intersect union difference
    empty? size contains (← getLCtx) (← getLocalInstances)
    genCondition freqCondition
    init.sampleName init.types cleanTypes init.subpat
  let .mk (_,cleanTypes) resConj ← cvb_thmConj_genMain
    fold empty insert insertMulti intersect union difference
    empty? size contains (← getLCtx) (← getLocalInstances)
    genCondition freqCondition
    init.sampleName init.types cleanTypes init.conj
  return .mk init.sampleName resRegB resRegF sT W tw resConj init.levelNum cleanTypes

#check 1

open System



def LeanGrow.genOfModuleName_thmKey (mod : Name) :=
  "genScore_thmK_" ++ mod.toUnderscoreString


@[specialize]
unsafe def generalize_back_cvbThm_ofModule
  {IdxCollType : Type} [Repr IdxCollType]
  (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β) (empty : IdxCollType)
  (insert : Nat → IdxCollType → IdxCollType)
  (insertMulti intersect union difference : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (size : IdxCollType → Nat) (contains : Nat → IdxCollType → Bool)
  (mod : Name)
  : IO Unit := do
  let cachePath ← findLeanGrowCacheDir
  let loadpath := FilePath.join cachePath ((FilePath.toString (LeanGrow.sampleNameOfModuleName_thmKey mod)))
  let (sams,reg) ← unpickle (ProcessedSamplesThmKey IdxCollType) loadpath
  let modules := #[mod]
  WithImportModules (modules.map (fun x => {module := x})) {} <| fun env => do
    stdMetaRun env do
      let .some midx := env.getModuleIdx? mod | panic s!"unknonw module {mod}"
      let cinfos := (env.header.moduleData[midx]!).constants
      let thmNames := cinfos.foldl (fun res info =>
        match info with
        | .thmInfo .. =>
          if info.name.blackListCaching env
          then res
          else res.push info.name
        | _ => res
        ) (Array.emptyWithCapacity cinfos.size)
      let res ← generalize_back_cvbThm_core
        fold empty insert insertMulti intersect union difference
        empty? size contains
        (fun w tot _ T _ => (w.toFloat / tot.toFloat ≥ 0.33) && (T != .sort 0))
        (fun w tot _ _ => (w.toFloat / tot.toFloat ≥ 0.33))
        sams
      let writepath := FilePath.join cachePath ((FilePath.toString (LeanGrow.genOfModuleName_thmKey mod)))
      pickle writepath res
  reg.free


#check 1


def LeanGrow.genOfModuleName_ghKey (mod : Name) :=
  "genScore_ghK_" ++ mod.toUnderscoreString


#check 1

@[specialize]
unsafe def generalize_back_cvbGoalHyp_ofModule
  {IdxCollType : Type} [Repr IdxCollType]
  (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β) (empty : IdxCollType)
  (insert : Nat → IdxCollType → IdxCollType)
  (insertMulti intersect union difference : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (size : IdxCollType → Nat) (contains : Nat → IdxCollType → Bool)
  (shiftAdd : IdxCollType → Nat → IdxCollType)
  (mod : Name)
  : IO Unit := do
  let cachePath ← findLeanGrowCacheDir
  let loadpath := FilePath.join cachePath ((FilePath.toString (LeanGrow.sampleNameOfModuleName_thmKey mod)))
  let (sams,reg) ← unpickle (ProcessedSamplesGHKey IdxCollType) loadpath
  let modules := #[mod]
  WithImportModules (modules.map (fun x => {module := x})) {} <| fun env => do
    stdMetaRun env do
      let .some midx := env.getModuleIdx? mod | panic s!"unknonw module {mod}"
      let cinfos := (env.header.moduleData[midx]!).constants
      let thmNames := cinfos.foldl (fun res info =>
        match info with
        | .thmInfo .. =>
          if info.name.blackListCaching env
          then res
          else res.push info.name
        | _ => res
        ) (Array.emptyWithCapacity cinfos.size)
      let res ← generalize_back_cvbGoalHyp_core
        fold empty insert insertMulti intersect union difference
        empty? size contains shiftAdd
        (fun w tot _ T _ => (w.toFloat / tot.toFloat ≥ 0.33) && (T != .sort 0))
        (fun w tot _ _ => (w.toFloat / tot.toFloat ≥ 0.33))
        sams
      let writepath := FilePath.join cachePath ((FilePath.toString (LeanGrow.genOfModuleName_thmKey mod)))
      pickle writepath res
  reg.free


#check 1


unsafe def generalize_back_cvbThm_ofModule_S
  (mod : Name)
  : IO Unit :=
    generalize_back_cvbThm_ofModule
      (fun is i f => is.foldl i (fun i s => f i.toNat s))
      UInt32Array.empty (fun x y => y.oInsert x.toUInt32)
      UInt32Array.union UInt32Array.inter UInt32Array.union
      UInt32Array.diff UInt32Array.isEmpty UInt32Array.size
      (fun x y => y.oContains x.toUInt32) mod

#check 1
#check UInt32Array.shiftAdd



unsafe def generalize_back_cvbGoalHyp_ofModule_S
  (mod : Name)
  : IO Unit :=
    generalize_back_cvbGoalHyp_ofModule
      (fun is i f => is.foldl i (fun i s => f i.toNat s))
      UInt32Array.empty (fun x y => y.oInsert x.toUInt32)
      UInt32Array.union UInt32Array.inter UInt32Array.union
      UInt32Array.diff UInt32Array.isEmpty UInt32Array.size
      (fun x y => y.oContains x.toUInt32)
      (fun x y => x.shiftAdd y.toUInt32)
      mod

#check 1
