
/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.SampleGenScore.Sample
import LeanGrow.Src.Caching.Score.Types
import LeanGrow.Src.Caching.Score.ConjecturableProcess


open Lean Meta


@[specialize]
def sampleClass_back_cvbThm_core
  (thmNames : Array Name) (conjPosTree : CTrie (List Nat))
  (depthDig depthStart depthStop : Nat) (deltaFuzz zetaFuzz : Option Nat)
  {IdxCollType : Type} [Repr IdxCollType] (empty : IdxCollType)
  (singleton : Nat → IdxCollType) (insert : Nat → IdxCollType → IdxCollType)
  (intersect  : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (init : ProcessedSamplesThmKey IdxCollType)
  : MetaM (ProcessedSamplesThmKey IdxCollType) := do
  mtracing
  let env ← getEnv
  let preS ← mkPreProCongr
  let mut L1 := ← getLCtx
  let mut L2 := ← getLocalInstances
  let mut samplesB : ListProd4 SampleData (List FVarId) Expr (List Expr) := .nil
  let mut samplesF : ListProd4 SampleData (List FVarId) Expr (List Expr) := .nil
  for thmName in thmNames do
    let .some (.thmInfo I) := env.find? thmName | throwError "Bad name"
    let .mk p fvs l1 l2 ← LambdaLetTelescope I.value 0 L1 L2
    let .mk res _ l1 l2 ← sampleCoreBack preS conjPosTree l1 l2 depthDig depthStart depthStop deltaFuzz zetaFuzz (.cons (.raw p) (fvs.map Expr.fvarId!).toList .nil) samplesB .nil
    samplesB := res
    let .mk res l1 l2 ← sampleCoreForw preS l1 l2 false depthDig depthStart depthStop deltaFuzz zetaFuzz (.cons (.raw p) (fvs.map Expr.fvarId!).toList .nil) samplesF
    samplesB := res
    L1 := l1
    L2 := l2
  mtrace on .zero with s!" done sampling"
  let .mk inter l1 l2 ← samplesB.foldlM (Prod3.mk init L1 L2)
    (fun sd _ goal hyps B@(.mk (.mk sampleName regularBack regularForw subpat conj lvlNum types) l1 l2) => do
      match sd with
      | .thm n =>
          let .mk goal (types, dict) l1 l2 ← goal.translateToLnodes l1 l2 sampleName types {}
          let .mk hyps (types, _) l1 l2 ← hyps.foldlM (fun (.mk L (types, dict) l1 l2) h => do
            let .mk h (types, dict) l1 l2 ← h.translateToLnodes l1 l2 sampleName types dict
            return .mk (h :: L) (types, dict) l1 l2
            ) (Prod4.mk [] (types, dict) l1 l2)
          let regularBack ← cvb_thms_sampleClassify
            empty singleton insert intersect empty? l1 l2 n goal hyps regularBack
          return .mk (.mk sampleName regularBack regularForw subpat conj lvlNum types) l1 l2
      | .induc n =>
          let sorted ← cvb_thms_sampleClassify_subPat
            empty singleton insert
            l1 l2 n goal sampleName types subpat
          return .mk (.mk sampleName regularBack regularForw sorted.2 conj lvlNum sorted.1) l1 l2
      | .thmC n cjs =>
          let .mk lvlNum types conj ← cvb_thmConj_sampleClassify
            empty singleton insert L1 L2 n cjs goal hyps sampleName (.mk lvlNum types conj)
          return .mk (.mk sampleName regularBack regularForw subpat conj lvlNum types) l1 l2
      | .none =>
          return B
      )
  let .mk res _ _ ← samplesF.foldlM (Prod3.mk inter l1 l2)
    (fun sd _ goal hyps B@(.mk (.mk sampleName regularBack regularForw subpat conj lvlNum types) l1 l2) => do
      match sd with
      | .thm n =>
          let .mk goal (types, dict) l1 l2 ← goal.translateToLnodes l1 l2 sampleName types {}
          let .mk hyps (types, _) l1 l2 ← hyps.foldlM (fun (.mk L (types, dict) l1 l2) h => do
            let .mk h (types, dict) l1 l2 ← h.translateToLnodes l1 l2 sampleName types dict
            return .mk (h :: L) (types, dict) l1 l2
            ) (Prod4.mk [] (types, dict) l1 l2)
          let regularForw ← cvb_thms_sampleClassify
            empty singleton insert intersect empty? l1 l2 n goal hyps regularForw
          return .mk (.mk sampleName regularBack regularForw subpat conj lvlNum types) l1 l2
      | _ =>
          return B
      )
  return res

#check 1
#check sampleCoreForw


open System

def LeanGrow.sampleNameOfModuleName_thmKey (mod : Name) :=
  "sampleScore_thmK_" ++ mod.toUnderscoreString

#check 1


@[specialize]
unsafe def sampleClass_back_cvbThm_ofModule
  (depthDig depthStart depthStop : Nat) (deltaFuzz zetaFuzz : Option Nat)
  {IdxCollType : Type} [Repr IdxCollType] (empty : IdxCollType)
  (singleton : Nat → IdxCollType) (insert : Nat → IdxCollType → IdxCollType)
  (intersect  : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (mod : Name)
  : IO Unit := do
  let cachePath ← findLeanGrowCacheDir
  let modules := #[mod]
  WithImportModules (modules.map (fun x => {module := x})) {} <| fun env => do
    stdMetaRun env do
      let modpath ← findOLean mod
      let (moddata, _) ← readModuleData modpath
      let imps := moddata.imports
      let mut regs : Array CompactedRegion := Array.replicate imps.size (0 : USize)
      let mut i := 0
      let mut data : Array (CTrie (List Nat)) := Array.replicate imps.size default
      for imp in imps do
        let path := FilePath.join cachePath ((FilePath.toString (LeanGrow.mkConjTreeName imp.module)))
        let (x, region) ← unpickle (CTrie (List Nat)) path
        regs := regs.set! i region
        data := data.set! i x
        i := i+1
      let conjTree := data.foldl (fun T t => CTrie.merge (fun x _ => x) T t) .empty
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
      let sampleName := .str .anonymous <| LeanGrow.sampleNameOfModuleName_thmKey mod
      let res ← sampleClass_back_cvbThm_core thmNames conjTree
        depthDig depthStart depthStop deltaFuzz zetaFuzz empty
        singleton insert intersect empty?
        (.mk sampleName .empty .empty .empty .empty 1 #[])
      let path := FilePath.join cachePath ((FilePath.toString (LeanGrow.sampleNameOfModuleName_thmKey mod)))
      pickle path res
      for reg in regs do
        reg.free


#check 1

unsafe def sampleClass_back_cvbThm_ofModule_S
  (depthDig depthStart depthStop : Nat) (deltaFuzz zetaFuzz : Option Nat)
  (mod : Name)
  : IO Unit :=
    sampleClass_back_cvbThm_ofModule
      depthDig depthStart depthStop deltaFuzz zetaFuzz
      UInt32Array.empty (fun n => UInt32Array.single n.toUInt32)
      (fun x y => y.oInsert x.toUInt32) UInt32Array.inter UInt32Array.isEmpty
      mod

#check 1


@[specialize]
def sampleClass_back_cvbGoalHyp_core
  (thmNames : Array Name) (conjPosTree : CTrie (List Nat))
  (depthDig depthStart depthStop : Nat) (deltaFuzz zetaFuzz : Option Nat)
  {IdxCollType : Type} [Repr IdxCollType]  (empty : IdxCollType)
  (singleton : Nat → IdxCollType) (insert : Nat → IdxCollType → IdxCollType)
  (intersect union: IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (head : IdxCollType → Nat)
  (init : ProcessedSamplesGHKey IdxCollType)
  : MetaM (ProcessedSamplesGHKey IdxCollType) := do
  mtracing
  let env ← getEnv
  let preS ← mkPreProCongr
  let mut L1 := ← getLCtx
  let mut L2 := ← getLocalInstances
  let mut samplesB : ListProd4 SampleData (List FVarId) Expr (List Expr) := .nil
  let mut samplesF : ListProd4 SampleData (List FVarId) Expr (List Expr) := .nil
  for thmName in thmNames do
    let .some (.thmInfo I) := env.find? thmName | throwError "Bad name"
    let .mk p fvs l1 l2 ← LambdaLetTelescope I.value 0 L1 L2
    let .mk res _ l1 l2 ← sampleCoreBack preS conjPosTree l1 l2 depthDig depthStart depthStop deltaFuzz zetaFuzz (.cons (.raw p) (fvs.map Expr.fvarId!).toList .nil) samplesB .nil
    samplesB := res
    let .mk res l1 l2 ← sampleCoreForw preS l1 l2 true depthDig depthStart depthStop deltaFuzz zetaFuzz (.cons (.raw p) (fvs.map Expr.fvarId!).toList .nil) samplesF
    samplesB := res
    L1 := l1
    L2 := l2
  mtrace on .zero with s!" done sampling"
  let .mk inter l1 l2 ← samplesB.foldlM (Prod3.mk init L1 L2)
    (fun sd _ goal hyps B@(.mk (.mk sampleName regularBack regularForw subpat conj lvlNum types) l1 l2) => do
      match sd with
      | .thm n =>
          let .mk goal (types, dict) l1 l2 ← goal.translateToLnodes l1 l2 sampleName types {}
          let .mk hyps (types, _) l1 l2 ← hyps.foldlM (fun (.mk L (types, dict) l1 l2) h => do
            let .mk h (types, dict) l1 l2 ← h.translateToLnodes l1 l2 sampleName types dict
            return .mk (h :: L) (types, dict) l1 l2
            ) (Prod4.mk [] (types, dict) l1 l2)
          let regularBack ← cvb_goal_hyp_sampleClassify
            empty singleton insert empty? intersect union head
            l1 l2 n goal hyps regularBack
          return .mk (.mk sampleName regularBack regularForw subpat conj lvlNum types) l1 l2
      | .induc n =>
          let sorted ← cvb_goal_hyp_sampleClassify_subPat
            empty singleton insert
            l1 l2 n goal sampleName types subpat
          return .mk (.mk sampleName regularBack regularForw (.mk sorted.2 sorted.3 sorted.4) conj lvlNum sorted.1) l1 l2
      | .thmC n cjs =>
          let .mk lvlNum types conj ← cvb_thmConj_sampleClassify
            empty singleton insert L1 L2 n cjs goal hyps sampleName (.mk lvlNum types conj)
          return .mk (.mk sampleName regularBack regularForw subpat conj lvlNum types) l1 l2
      | .none =>
          return B
      )
  let .mk res _ _ ← samplesF.foldlM (Prod3.mk inter l1 l2)
    (fun sd _ goal hyps B@(.mk (.mk sampleName regularBack regularForw subpat conj lvlNum types) l1 l2) => do
      match sd with
      | .thm n =>
          let .mk goal (types, dict) l1 l2 ← goal.translateToLnodes l1 l2 sampleName types {}
          let .mk hyps (types, _) l1 l2 ← hyps.foldlM (fun (.mk L (types, dict) l1 l2) h => do
            let .mk h (types, dict) l1 l2 ← h.translateToLnodes l1 l2 sampleName types dict
            return .mk (h :: L) (types, dict) l1 l2
            ) (Prod4.mk [] (types, dict) l1 l2)
          let regularForw ← cvb_goal_hyp_sampleClassify
            empty singleton insert empty? intersect union head
            l1 l2 n goal hyps regularForw
          return .mk (.mk sampleName regularBack regularForw subpat conj lvlNum types) l1 l2
      | _ =>
          return B
      )
  return res

#check 1



def LeanGrow.sampleNameOfModuleName_ghKey (mod : Name) :=
  "sampleScore_ghK_" ++ mod.toUnderscoreString

#check 1


@[specialize]
unsafe def sampleClass_back_cvbGoalHyp_ofModule
  (depthDig depthStart depthStop : Nat) (deltaFuzz zetaFuzz : Option Nat)
  {IdxCollType : Type} [Repr IdxCollType] (empty : IdxCollType)
  (singleton : Nat → IdxCollType) (insert : Nat → IdxCollType → IdxCollType)
  (intersect union: IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (head : IdxCollType → Nat)
  (mod : Name)
  : IO Unit := do
  let cachePath ← findLeanGrowCacheDir
  let modules := #[mod]
  WithImportModules (modules.map (fun x => {module := x})) {} <| fun env => do
    stdMetaRun env do
      let modpath ← findOLean mod
      let (moddata, _) ← readModuleData modpath
      let imps := moddata.imports
      let mut regs : Array CompactedRegion := Array.replicate imps.size (0 : USize)
      let mut i := 0
      let mut data : Array (CTrie (List Nat)) := Array.replicate imps.size default
      for imp in imps do
        let path := FilePath.join cachePath ((FilePath.toString (LeanGrow.mkConjTreeName imp.module)))
        let (x, region) ← unpickle (CTrie (List Nat)) path
        regs := regs.set! i region
        data := data.set! i x
        i := i+1
      let conjTree := data.foldl (fun T t => CTrie.merge (fun x _ => x) T t) .empty
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
      let sampleName := .str .anonymous <| LeanGrow.sampleNameOfModuleName_ghKey mod
      let res ← sampleClass_back_cvbGoalHyp_core thmNames conjTree
        depthDig depthStart depthStop deltaFuzz zetaFuzz empty
        singleton insert intersect union empty? head
        (.mk sampleName (.mk 0 .dead #[]) (.mk 0 .dead #[]) (.mk 0 .dead #[]) .empty 1 #[])
      let path := FilePath.join cachePath ((FilePath.toString (LeanGrow.sampleNameOfModuleName_ghKey mod)))
      pickle path res
      for reg in regs do
        reg.free


#check 1


unsafe def sampleClass_back_cvbGoalHyp_ofModule_S
  (depthDig depthStart depthStop : Nat) (deltaFuzz zetaFuzz : Option Nat)
  (mod : Name)
  : IO Unit :=
    sampleClass_back_cvbGoalHyp_ofModule
      depthDig depthStart depthStop deltaFuzz zetaFuzz
      UInt32Array.empty (fun n => UInt32Array.single n.toUInt32)
      (fun x y => y.oInsert x.toUInt32) UInt32Array.inter
      UInt32Array.union UInt32Array.isEmpty
      (fun x => x[0]!.toNat) mod


#check 1
