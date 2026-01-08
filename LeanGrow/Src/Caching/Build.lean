
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrowBeta.Caching.Formating.Process
import LeanGrowBeta.Data.SetTrie.Specialize
import LeanGrowBeta.Utils.Lean.ImportExport
import LeanGrowBeta.Utils.Std.Name
import LeanGrowBeta.Utils.Lean.Blacklisting

open Lean Meta

variable {IdxCollType : Type _}


structure ModuleCacheState (IdxCollType : Type _) where
  thm_data : Array ThmFormat
  thmNameToIdx : CTrie (List Nat)
  thmNameToHypIdx : CTrie (List Nat)
  stdBackPaIn : PaIn IdxCollType
  stdForwSetTrie : SetTrie ThmFormat (PaIn IdxCollType)
  stdForwSetTrie_idxToThmIdx : Array Nat
  rwBackPaIn : PaIn IdxCollType
  rwForwPaIn : PaIn IdxCollType
deriving Inhabited

structure ModuleCacheStatePartial (IdxCollType : Type _) where
  Cstop : Nat
  countThm : Nat
  countHyps : Nat
  thm_data : Array ThmFormat
  thmNameToIdx : CTrie (List Nat)
  thmNameToHypIdx : CTrie (List Nat)
  stdBackPaIn : PaIn IdxCollType
  stdForwSetTrie : ListProd (PaIn IdxCollType) ThmFormat
  stdForwSetTrie_idxToThmIdx : Array Nat
  rwBackPaIn : PaIn IdxCollType
  rwForwPaIn : PaIn IdxCollType
deriving Inhabited




@[specialize, inline]
partial def buildCachDataForCore [Repr IdxCollType]
  (emptyCol : IdxCollType)
  (singleton : Nat → IdxCollType) (insert : Nat → IdxCollType → IdxCollType)
  (module : Name) (cinfos : Array ConstantInfo) (Cstart Cstop : Nat)
  (sofarBack : PaIn IdxCollType) (formats : Array ThmFormat)
  (sofarBackRW : PaIn IdxCollType) (countThm : Nat) (sofarFwd : ListProd (PaIn IdxCollType) ThmFormat)
  (hyptothm : Array Nat) (sofarFwdRW : PaIn IdxCollType) (countHyps : Nat) (thmNameToIdx thmNameToHypIdx : CTrie (List Nat))
  : MetaM (ModuleCacheStatePartial IdxCollType) :=
  let rec @[specialize] go (cinfoI : Nat) (sofarBack : PaIn IdxCollType) (formats : Array ThmFormat)
    (sofarBackRW : PaIn IdxCollType) (countThm : Nat) (sofarFwd : ListProd (PaIn IdxCollType) ThmFormat)
    (hyptothm : Array Nat) (sofarFwdRW : PaIn IdxCollType) (countHyps : Nat) (thmNameToIdx thmNameToHypIdx : CTrie (List Nat))
    : MetaM (ModuleCacheStatePartial IdxCollType) := do
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
      mtrace on .zero with s!"[buildCachDataFor] on decl {cinfo.name} with idx {countThm}"
      if cinfo.name.blackListCaching
      then
        mtrace on .zero with s!"[buildCachDataFor] blacklisted !"
        go (cinfoI + 1) sofarBack formats sofarBackRW countThm sofarFwd hyptothm sofarFwdRW countHyps thmNameToIdx thmNameToHypIdx
      else
        let (rwWithSinkNotInGoal, data) ← processForCache module countThm cinfo
        mtrace on .zero with s!"[buildCachDataFor] passed processForCache"
        match data with
        | d@(.std _ _ _ hyps mctx _ goal sinks) :: [] =>
            mtrace on .zero with s!"[buildCachDataFor] std case"
            mtrace on .one with s!"[buildCachDataFor] sinks {sinks}"
            let formats := formats.push d
            mctx.load -- paranoina ?
            let ⟨sofarBack,_,_⟩ ← sofarBack.insert (← getLCtx) (← getLocalInstances) goal countThm emptyCol singleton insert
            mtrace on .zero with s!"[buildCachDataFor] add goal to back"
            let HforFwdPaIn := sinks.foldl (fun S s => match hyps[s]! with | .inst .. => S | .reg type => (type) :: S) []
            let (FwdPaIn,_) ← HforFwdPaIn.foldlM (fun (T,i) e => do
              let ⟨res,_,_⟩ ← T.insert (← getLCtx) (← getLocalInstances) e i emptyCol singleton insert
              mtrace on .zero with s!"[buildCachDataFor] for forw, added hyp {← ppExpr e}"
              return (res, i+1)) (PaIn.dead, countHyps)
            let sofarFwd := .cons FwdPaIn d sofarFwd
            let hyptothm := (hyptothm.pushN countThm) HforFwdPaIn.length
            let ciN := cinfo.name.toString.toUTF8
            let thmNameToIdx := thmNameToIdx.insert ciN [countThm]
            let countThm := countThm + 1
            let thmNameToHypIdx := thmNameToHypIdx.insert ciN (List.Ico countHyps (countHyps + HforFwdPaIn.length))
            let countHyps := countHyps + HforFwdPaIn.length
            go (cinfoI + 1) sofarBack formats sofarBackRW countThm sofarFwd hyptothm sofarFwdRW countHyps thmNameToIdx thmNameToHypIdx
        | fst@(.rw _ _ _ goal replacement _ mctx _ _) :: snd :: [] => do
            mtrace on .zero with s!"[buildCachDataFor] rw case"
            let formats := (formats.push fst).push snd
            mctx.load -- paranoina ?
            mtrace on .zero with s!"[buildCachDataFor] rwWithSinkNotInGoal {rwWithSinkNotInGoal} "
            if !rwWithSinkNotInGoal
            then -- handle forward rws in LeanGrowBeta
              let ⟨sofarBackRW,_,_⟩ ← sofarBackRW.insert (← getLCtx) (← getLocalInstances) goal countThm emptyCol singleton insert
              mtrace on .zero with s!"[buildCachDataFor] added left to back"
              let ⟨sofarFwdRW,_,_⟩ ← sofarFwdRW.insert (← getLCtx) (← getLocalInstances) goal countThm emptyCol singleton insert
              mtrace on .zero with s!"[buildCachDataFor] added left to forw"
              let countThm := countThm + 1
              let ⟨sofarBackRW,_,_⟩ ← sofarBackRW.insert (← getLCtx) (← getLocalInstances) replacement countThm emptyCol singleton insert
              mtrace on .zero with s!"[buildCachDataFor] added right to back"
              let ⟨sofarFwdRW,_,_⟩ ← sofarFwdRW.insert (← getLCtx) (← getLocalInstances) replacement countThm emptyCol singleton insert
              mtrace on .zero with s!"[buildCachDataFor] added rigth to forw"
              let thmNameToIdx := thmNameToIdx.insert cinfo.name.toString.toUTF8 [countThm,countThm - 1]
              let countThm := countThm + 1
              go (cinfoI + 1) sofarBack formats sofarBackRW countThm sofarFwd hyptothm sofarFwdRW countHyps thmNameToIdx thmNameToHypIdx
            else
              let ⟨sofarBackRW,_,_⟩ ← sofarBackRW.insert (← getLCtx) (← getLocalInstances) goal countThm emptyCol singleton insert
              mtrace on .zero with s!"[buildCachDataFor] added left to back"
              let countThm := countThm + 1
              let ⟨sofarBackRW,_,_⟩ ← sofarBackRW.insert (← getLCtx) (← getLocalInstances) replacement countThm emptyCol singleton insert
              mtrace on .zero with s!"[buildCachDataFor] added right to back"
              let thmNameToIdx := thmNameToIdx.insert cinfo.name.toString.toUTF8 [countThm,countThm - 1]
              let countThm := countThm + 1
              go (cinfoI + 1) sofarBack formats sofarBackRW countThm sofarFwd hyptothm sofarFwdRW countHyps thmNameToIdx thmNameToHypIdx
        | _ => throwError s!"[buildCachDataFor] unsupported format ?!?"
  Meta.withUnlimitedHeartbeats do
  mtrace on .zero with s!"[buildCachDataFor] unlimited heartbeats"
  Meta.withResetRecDepth do
    mtrace on .zero with s!"[buildCachDataFor] reset rec depth"
    go Cstart sofarBack formats sofarBackRW countThm sofarFwd hyptothm sofarFwdRW countHyps thmNameToIdx thmNameToHypIdx


def LeanGrow.mkCacheName : Name → String :=
  (fun n => s!"LeanGrow_ThmFormatQueryCache{n.toUnderscoreString}")

def LeanGrow.mkPartialCacheName : Name → String :=
  (fun n => s!"LeanGrow_ThmFormatQueryPartialCache{n.toUnderscoreString}")

#print Import

open System

@[specialize, inline]
unsafe def buildPartialCacheData [Repr IdxCollType]
  (emptyCol : IdxCollType)
  (singleton : Nat → IdxCollType) (insert : Nat → IdxCollType → IdxCollType)
  (modules : Array Name) (StepSize : Nat) (opts : Options := {}) : IO Unit :=
  withImportModules (modules.map (fun x => {module := x})) opts <| fun env => do
    stdMetaRun env do
      let cachePath ← findLeanGrowCacheDir
      let finalPath := FilePath.join cachePath (FilePath.toString "withUnpickleTracing.txt")
      let mut regs : Array CompactedRegion := Array.replicate modules.size (0 : USize)
      let mut i := 0
      for module in modules do
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
          i := i+1
        else
          let (x, region) ← unpickle (ModuleCacheStatePartial IdxCollType) path
          regs := regs.set! i region
          let .some midx := env.getModuleIdx? module | throwError s!"[buildCachData] unknonw module {module}"
          let cinfos := (env.header.moduleData[midx]!).constants
          if x.Cstop ≥ cinfos.size
          then
            throwError s!"[buildCachData] no more steps necessary"
          else
            let res ← buildCachDataForCore emptyCol singleton insert
                        module cinfos
                        x.Cstop (x.Cstop + StepSize)
                        x.stdBackPaIn x.thm_data x.rwBackPaIn x.countThm x.stdForwSetTrie  x.stdForwSetTrie_idxToThmIdx x.rwForwPaIn x.countHyps x.thmNameToIdx x.thmNameToHypIdx
            let finalPath := FilePath.join cachePath (FilePath.toString (LeanGrow.mkPartialCacheName module))
            pickle finalPath res
            i := i+1
      for reg in regs do
        reg.free



@[specialize, inline]
unsafe def buildPartialCacheDataS (modules : Array Name) (StepSize : Nat)  (opts : Options := {}) : IO Unit :=
  buildPartialCacheData
    [] (fun x => [x]) List.orderedInsertOrLeave
    modules StepSize opts

@[specialize, inline]
unsafe def buildCacheData [Repr IdxCollType]
  (toList : IdxCollType → List Nat)
  (insertMulti intersect union difference : IdxCollType → IdxCollType → IdxCollType)
  (emptyCol : IdxCollType) (empty? : IdxCollType → Bool) (size : IdxCollType → Nat)
  (modules : Array Name) (opts : Options := {}) : IO Unit :=
  withImportModules (modules.map (fun x => {module := x})) opts <| fun env => do
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
            let hypIndToThm : Nat → ThmFormat := (fun n =>
              let thmIdx := x.stdForwSetTrie_idxToThmIdx[n]!
              x.thm_data[thmIdx]!)
            let res ← SetTrieP.ofList (← getLCtx) (← getLocalInstances) thmData toList hypIndToThm insertMulti intersect union difference emptyCol empty? size x.stdForwSetTrie
            mtrace on .zero with s!"[buildCachDataFor] built forward SetTrie"
            let final : ModuleCacheState IdxCollType :=
              ⟨x.thm_data, x.thmNameToIdx, x.thmNameToHypIdx, x.stdBackPaIn, res, x.stdForwSetTrie_idxToThmIdx, x.rwBackPaIn, x.rwForwPaIn⟩
            return (final, s!"Cached {module} !")
            )
        i := i+1
      for reg in regs do
        reg.free

@[specialize, inline]
unsafe def buildCacheDataS (modules : Array Name) (opts : Options := {}) : IO Unit :=
  buildCacheData
    id (fun x y => x.foldl (fun R a => (R.orderedInsertOrLeave a)) y) (List.orderedIntersect)
    (List.orderedUnion) (List.orderedDiff) [] List.isEmpty List.length
    modules opts
