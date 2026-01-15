
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Caching.Formating.Process
import LeanGrow.Src.Caching.Query.PaInGMergeSpe
import LeanGrow.Src.Utils.Lean.ImportExport
import LeanGrow.Src.Utils.Std.Name
import LeanGrow.Src.Utils.Lean.Blacklisting

open Lean Meta

variable {IdxCollType : Type _}


structure ModuleCacheState (IdxCollType : Type _) where
  thm_data : Array ThmFormat
  thmNameToIdx : CTrie (List Nat)
  thmNameToHypIdx : CTrie (List Nat)
  stdBackPaIn : PaInG IdxCollType
  stdForwSetTrie : SetTrieP ThmFormat IdxCollType PaInG
  stdForwSetTrie_idxToThmIdx : Array Nat
  rwBackPaIn : PaInG IdxCollType
  rwForwPaIn : PaInG IdxCollType
deriving Inhabited

structure ModuleCacheStatePartial (IdxCollType : Type _) where
  Cstop : Nat
  countThm : Nat
  countHyps : Nat
  thm_data : Array ThmFormat
  thmNameToIdx : CTrie (List Nat)
  thmNameToHypIdx : CTrie (List Nat)
  stdBackPaIn : PaInG IdxCollType
  stdForwSetTrie : ListProd (PaInG IdxCollType) ThmFormat
  stdForwSetTrie_idxToThmIdx : Array Nat
  rwBackPaIn : PaInG IdxCollType
  rwForwPaIn : PaInG IdxCollType
deriving Inhabited


-- #exit

@[specialize, inline]
partial def buildCachDataForCore [Repr IdxCollType]
  (emptyCol : IdxCollType)
  (singleton : Nat → IdxCollType) (insert : Nat → IdxCollType → IdxCollType)
  (module : Name) (cinfos : Array ConstantInfo) (Cstart Cstop : Nat)
  (sofarBack : PaInG IdxCollType) (formats : Array ThmFormat)
  (sofarBackRW : PaInG IdxCollType) (countThm : Nat) (sofarFwd : ListProd (PaInG IdxCollType) ThmFormat)
  (hyptothm : Array Nat) (sofarFwdRW : PaInG IdxCollType) (countHyps : Nat) (thmNameToIdx thmNameToHypIdx : CTrie (List Nat))
  : MetaM (ModuleCacheStatePartial IdxCollType) :=
  let rec @[specialize] inner (ciN : ByteArray)
    (sofarBack : PaInG IdxCollType) (formats : Array ThmFormat)
    (sofarBackRW : PaInG IdxCollType) (countThm : Nat) (sofarFwd : ListProd (PaInG IdxCollType) ThmFormat)
    (hyptothm : Array Nat) (sofarFwdRW : PaInG IdxCollType) (countHyps : Nat) (thmNameToIdx thmNameToHypIdx : CTrie (List Nat))
    (rwWithSinkNotInGoal : Bool) (data : ListProd badUniType ThmFormat)
    : MetaM (Prod10 _ _ _ _ _ _ _ _ _ _) := do
    mtracing
    match data with
    | .nil =>
        return .mk sofarBack formats sofarBackRW countThm sofarFwd hyptothm sofarFwdRW countHyps thmNameToIdx thmNameToHypIdx
    | .cons badu d@(.std _ _ _ hyps _ _ goal sinks ..) more =>
        mtrace on .zero with s!" std case"
        mtrace on .zero with s!" badu {repr badu}"
        mtrace on .one with s!" sinks {sinks}"
        match badu with
        | .both =>
          inner ciN sofarBack formats sofarBackRW countThm sofarFwd hyptothm sofarFwdRW countHyps thmNameToIdx thmNameToHypIdx rwWithSinkNotInGoal more
        | .fwdOnly =>
          let formats := formats.push d
          let ⟨sofarBack,_,_⟩ ← sofarBack.insert (← getLCtx) (← getLocalInstances) goal countThm emptyCol singleton insert
          mtrace on .zero with s!" add goal to back"
          -- let ciN := cinfo.name.toString.toUTF8
          let thmNameToIdx := thmNameToIdx.insert ciN [countThm]
          let countThm := countThm + 1
          inner ciN sofarBack formats sofarBackRW countThm sofarFwd hyptothm sofarFwdRW countHyps thmNameToIdx thmNameToHypIdx rwWithSinkNotInGoal more
        | .bckOnly =>
          let formats := formats.push d
          let HforFwdPaIn := sinks.foldl (fun S s => match hyps[s]! with | .inst .. => S | .reg type => (type) :: S) []
          let (FwdPaIn,_) ← HforFwdPaIn.foldlM (fun (T,i) e => do
            let ⟨res,_,_⟩ ← T.insert (← getLCtx) (← getLocalInstances) e i emptyCol singleton insert
            mtrace on .zero with s!" for forw, added hyp {← ppExpr e}"
            return (res, i+1)) (PaInG.dead, countHyps)
          let sofarFwd := .cons FwdPaIn d sofarFwd
          let hyptothm := (hyptothm.pushN countThm) HforFwdPaIn.length
          -- let ciN := cinfo.name.toString.toUTF8
          let thmNameToIdx := thmNameToIdx.insert ciN [countThm]
          let countThm := countThm + 1
          let thmNameToHypIdx := thmNameToHypIdx.insert ciN (List.Ico countHyps (countHyps + HforFwdPaIn.length))
          let countHyps := countHyps + HforFwdPaIn.length
          inner ciN sofarBack formats sofarBackRW countThm sofarFwd hyptothm sofarFwdRW countHyps thmNameToIdx thmNameToHypIdx rwWithSinkNotInGoal more
        | .no =>
          let formats := formats.push d
          let ⟨sofarBack,_,_⟩ ← sofarBack.insert (← getLCtx) (← getLocalInstances) goal countThm emptyCol singleton insert
          mtrace on .zero with s!" add goal to back"
          let HforFwdPaIn := sinks.foldl (fun S s => match hyps[s]! with | .inst .. => S | .reg type => (type) :: S) []
          let (FwdPaIn,_) ← HforFwdPaIn.foldlM (fun (T,i) e => do
            let ⟨res,_,_⟩ ← T.insert (← getLCtx) (← getLocalInstances) e i emptyCol singleton insert
            mtrace on .zero with s!" for forw, added hyp {← ppExpr e}"
            return (res, i+1)) (PaInG.dead, countHyps)
          let sofarFwd := .cons FwdPaIn d sofarFwd
          let hyptothm := (hyptothm.pushN countThm) HforFwdPaIn.length
          -- let ciN := cinfo.name.toString.toUTF8
          let thmNameToIdx := thmNameToIdx.insert ciN [countThm]
          let countThm := countThm + 1
          let thmNameToHypIdx := thmNameToHypIdx.insert ciN (List.Ico countHyps (countHyps + HforFwdPaIn.length))
          let countHyps := countHyps + HforFwdPaIn.length
          inner ciN sofarBack formats sofarBackRW countThm sofarFwd hyptothm sofarFwdRW countHyps thmNameToIdx thmNameToHypIdx rwWithSinkNotInGoal more
    | .cons badu fst@(.rw _ _ _ goal ..) more => do
        mtrace on .zero with s!" rw case"
        mtrace on .zero with s!" badu {repr badu}"
        match badu with
        | .no =>
          let formats := (formats.push fst)
          mtrace on .zero with s!" rwWithSinkNotInGoal {rwWithSinkNotInGoal} "
          if !rwWithSinkNotInGoal
          then
            let ⟨sofarBackRW,_,_⟩ ← sofarBackRW.insert (← getLCtx) (← getLocalInstances) goal countThm emptyCol singleton insert
            mtrace on .zero with s!" added left to back"
            let ⟨sofarFwdRW,_,_⟩ ← sofarFwdRW.insert (← getLCtx) (← getLocalInstances) goal countThm emptyCol singleton insert
            mtrace on .zero with s!" added left to forw"
            let thmNameToIdx := thmNameToIdx.insert ciN [countThm]
            let countThm := countThm + 1
            inner ciN sofarBack formats sofarBackRW countThm sofarFwd hyptothm sofarFwdRW countHyps thmNameToIdx thmNameToHypIdx rwWithSinkNotInGoal more
          else
            let ⟨sofarBackRW,_,_⟩ ← sofarBackRW.insert (← getLCtx) (← getLocalInstances) goal countThm emptyCol singleton insert
            mtrace on .zero with s!" added left to back"
            let thmNameToIdx := thmNameToIdx.insert ciN [countThm]
            let countThm := countThm + 1
            inner ciN sofarBack formats sofarBackRW countThm sofarFwd hyptothm sofarFwdRW countHyps thmNameToIdx thmNameToHypIdx rwWithSinkNotInGoal more
        | _ =>
          inner ciN sofarBack formats sofarBackRW countThm sofarFwd hyptothm sofarFwdRW countHyps thmNameToIdx thmNameToHypIdx rwWithSinkNotInGoal more
  let rec @[specialize] go (cinfoI : Nat) (sofarBack : PaInG IdxCollType) (formats : Array ThmFormat)
    (sofarBackRW : PaInG IdxCollType) (countThm : Nat) (sofarFwd : ListProd (PaInG IdxCollType) ThmFormat)
    (hyptothm : Array Nat) (sofarFwdRW : PaInG IdxCollType) (countHyps : Nat) (thmNameToIdx thmNameToHypIdx : CTrie (List Nat))
    : MetaM (ModuleCacheStatePartial IdxCollType) := do
    mtracing
    if cinfoI ≥ cinfos.size || cinfoI ≥ Cstop
    then
      let final : ModuleCacheStatePartial IdxCollType :=
          {Cstop := Cstop
           countThm := countThm
           countHyps := countHyps
           thm_data := formats
           thmNameToIdx := thmNameToIdx
           thmNameToHypIdx := thmNameToHypIdx
           stdBackPaIn := sofarBack
           stdForwSetTrie := sofarFwd
           stdForwSetTrie_idxToThmIdx := hyptothm
           rwBackPaIn := sofarBackRW
           rwForwPaIn := sofarFwdRW
          }
      return final
    else
      let cinfo := cinfos[cinfoI]!
      --mtrace on .zero with s!" on decl {cinfo.name} with idx {countThm}"
      -- ↑ even with tracing disabled, causes overflow at execution ...
      match cinfo with
      | .thmInfo .. | .axiomInfo .. =>
        if cinfo.name.blackListCaching (← getEnv)
        then
          mtrace on .zero with s!" blacklisted !"
          go (cinfoI + 1) sofarBack formats sofarBackRW countThm sofarFwd hyptothm sofarFwdRW countHyps thmNameToIdx thmNameToHypIdx
        else
          let .mk rwWithSinkNotInGoal data _ _ ← processForCache module countThm cinfo
          mtrace on .zero with s!" passed processForCache"
          let ciN := cinfo.name.toString.toUTF8
          let .mk sofarBack formats sofarBackRW countThm sofarFwd hyptothm sofarFwdRW countHyps thmNameToIdx thmNameToHypIdx ← inner ciN sofarBack formats sofarBackRW countThm sofarFwd hyptothm sofarFwdRW countHyps thmNameToIdx thmNameToHypIdx rwWithSinkNotInGoal data
          go (cinfoI + 1) sofarBack formats sofarBackRW countThm sofarFwd hyptothm sofarFwdRW countHyps thmNameToIdx thmNameToHypIdx
        | .ctorInfo .. =>
          if cinfo.name.blackListCaching (← getEnv)
          then
            mtrace on .zero with s!" blacklisted !"
            go (cinfoI + 1) sofarBack formats sofarBackRW countThm sofarFwd hyptothm sofarFwdRW countHyps thmNameToIdx thmNameToHypIdx
          else
            if ← isProp cinfo.type
            then
              let .mk rwWithSinkNotInGoal data _ _ ← processForCache module countThm cinfo
              mtrace on .zero with s!" passed processForCache"
              let ciN := cinfo.name.toString.toUTF8
              let .mk sofarBack formats sofarBackRW countThm sofarFwd hyptothm sofarFwdRW countHyps thmNameToIdx thmNameToHypIdx ← inner ciN sofarBack formats sofarBackRW countThm sofarFwd hyptothm sofarFwdRW countHyps thmNameToIdx thmNameToHypIdx rwWithSinkNotInGoal data
              go (cinfoI + 1) sofarBack formats sofarBackRW countThm sofarFwd hyptothm sofarFwdRW countHyps thmNameToIdx thmNameToHypIdx
            else
              mtrace on .zero with s!" non prop ctor !"
              go (cinfoI + 1) sofarBack formats sofarBackRW countThm sofarFwd hyptothm sofarFwdRW countHyps thmNameToIdx thmNameToHypIdx
        | _ =>
          mtrace on .zero with s!" skip !"
          go (cinfoI + 1) sofarBack formats sofarBackRW countThm sofarFwd hyptothm sofarFwdRW countHyps thmNameToIdx thmNameToHypIdx
  Meta.withUnlimitedHeartbeats do
  mtracing
  mtrace on .zero with s!" unlimited heartbeats"
  Meta.withResetRecDepth do
    mtrace on .zero with s!" reset rec depth"
    go Cstart sofarBack formats sofarBackRW countThm sofarFwd hyptothm sofarFwdRW countHyps thmNameToIdx thmNameToHypIdx



def LeanGrow.mkCacheName : Name → String :=
  (fun n => s!"LeanGrow_ThmFormatQueryCache_{n.toUnderscoreString}")

def LeanGrow.mkPartialCacheName : Name → String :=
  (fun n => s!"LeanGrow_ThmFormatQueryPartialCache_{n.toUnderscoreString}")

#print Import

open System

@[specialize, inline]
unsafe def buildPartialCacheData [Repr IdxCollType]
  (emptyCol : IdxCollType)
  (singleton : Nat → IdxCollType) (insert : Nat → IdxCollType → IdxCollType)
  (module : Name) (StepSize : Nat) (opts : Options := {}) : IO Unit :=
  let modules := #[module]
  withImportModules (modules.map (fun x => {module := x})) opts <| fun env => do
    stdMetaRun env do
      let cachePath ← findLeanGrowCacheDir
      let finalPath := FilePath.join cachePath (FilePath.toString "withUnpickleTracing.txt")
      let path := FilePath.join cachePath ⟨LeanGrow.mkPartialCacheName module⟩
      if !(← path.pathExists)
      then
        let .some midx := env.getModuleIdx? module | throwError s!"[buildCachData] unknonw module {module}"
        let cinfos := (env.header.moduleData[midx]!).constants
        let res ← buildCachDataForCore emptyCol singleton insert
                    module cinfos
                    0 StepSize
                    .dead #[] .dead 0 .nil #[] .dead 0 .empty .empty
        let finalPath := FilePath.join cachePath (FilePath.toString (LeanGrow.mkPartialCacheName module))
        pickle finalPath res
      else
        let (x, region) ← unpickle (ModuleCacheStatePartial IdxCollType) path
        let .some midx := env.getModuleIdx? module | throwError s!"[buildCachData] unknonw module {module}"
        let cinfos := (env.header.moduleData[midx]!).constants
        if x.Cstop ≥ cinfos.size
        then
          throwError s!"[buildPartialCacheData] no more steps necessary"
        else
          let res ← buildCachDataForCore emptyCol singleton insert
                      module cinfos
                      x.Cstop (x.Cstop + StepSize)
                      x.stdBackPaIn x.thm_data x.rwBackPaIn x.countThm x.stdForwSetTrie  x.stdForwSetTrie_idxToThmIdx x.rwForwPaIn x.countHyps x.thmNameToIdx x.thmNameToHypIdx
          let finalPath := FilePath.join cachePath (FilePath.toString (LeanGrow.mkPartialCacheName module))
          pickle finalPath res
        region.free

#check 1


@[specialize, inline]
unsafe def buildPartialCacheDataS (module : Name) (StepSize : Nat)  (opts : Options := {}) : IO Unit :=
  buildPartialCacheData
    UInt32Array.empty (fun x => UInt32Array.single x.toUInt32) (fun x y => y.oInsert x.toUInt32)
    module StepSize opts

#check 1

@[specialize, inline]
unsafe def buildPartialCacheDataFull [Repr IdxCollType]
  (emptyCol : IdxCollType)
  (singleton : Nat → IdxCollType) (insert : Nat → IdxCollType → IdxCollType)
  (module : Name) (opts : Options := {}) : IO Unit :=
  let modules := #[module]
  WithImportModules (modules.map (fun x => {module := x})) opts <| fun env => do
    stdMetaRun env do
      let cachePath ← findLeanGrowCacheDir
      let finalPath := FilePath.join cachePath (FilePath.toString "withUnpickleTracing.txt")
      let path := FilePath.join cachePath ⟨LeanGrow.mkPartialCacheName module⟩
      let .some midx := env.getModuleIdx? module | throwError s!"[buildCachData] unknonw module {module}"
      let cinfos := (env.header.moduleData[midx]!).constants
      let res ← buildCachDataForCore emptyCol singleton insert
                  module cinfos
                  0 cinfos.size
                  .dead #[] .dead 0 .nil #[] .dead 0 .empty .empty
      let finalPath := FilePath.join cachePath (FilePath.toString (LeanGrow.mkPartialCacheName module))
      pickle finalPath res

unsafe def buildPartialCacheDataFullS (module : Name) (opts : Options := {}) : IO Unit :=
  buildPartialCacheDataFull
    UInt32Array.empty (fun x => UInt32Array.single x.toUInt32) (fun x y => y.oInsert x.toUInt32)
    module opts


@[specialize, inline]
unsafe def buildCacheData [Repr IdxCollType]
  (intersect union difference : IdxCollType → IdxCollType → IdxCollType)
  (emptyCol : IdxCollType) (empty? : IdxCollType → Bool) (size : IdxCollType → Nat)
  (module : Name) (opts : Options := {}) : IO Unit :=
  let modules := #[module]
  WithImportModules (modules.map (fun x => {module := x})) opts <| fun env => do
    stdMetaRun env do
      let cachePath ← findLeanGrowCacheDir
      let mut regs : Array CompactedRegion := Array.replicate modules.size (0 : USize)
      let mut i := 0
      for module in modules do
        let path := FilePath.join cachePath ⟨LeanGrow.mkPartialCacheName module⟩
        let (x, region) ← unpickle (ModuleCacheStatePartial IdxCollType) path
        regs := regs.set! i region
        stdImportTracePicklePerImport
          modules opts
          LeanGrow.mkCacheName
          (fun module => do
            let thmData : CTrie (Array ThmFormat) :=
              CTrie.insert .empty (module.toString.toUTF8) x.thm_data
            let res ← SetTriePGSpe.ofList thmData intersect union difference emptyCol empty? size x.stdForwSetTrie
            let final : ModuleCacheState IdxCollType :=
              ⟨x.thm_data, x.thmNameToIdx, x.thmNameToHypIdx, x.stdBackPaIn, res, x.stdForwSetTrie_idxToThmIdx, x.rwBackPaIn, x.rwForwPaIn⟩
            return (final, s!"Cached {module} !")
            )
        i := i+1
      for reg in regs do
        reg.free


unsafe def buildCacheDataS (modules : Name) (opts : Options := {}) : IO Unit :=
  buildCacheData
    (UInt32Array.inter) (UInt32Array.union) (UInt32Array.diff) UInt32Array.empty UInt32Array.isEmpty UInt32Array.size
    modules opts
