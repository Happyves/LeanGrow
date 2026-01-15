
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Caching.Query.Build
import LeanGrow.Src.Data.PathIndexG.Indexing


open Lean Meta

variable {IdxCollType : Type _}


structure mergeCoreData (IdxCollType : Type _) where
  thmIdxOff : Nat
  hypIdxOff : Nat
  data : ModuleCacheState IdxCollType
  thmData : CTrie (Array ThmFormat)


@[specialize, inline]
def ModuleCacheState.mergeCore [Repr IdxCollType]
  (union : IdxCollType → IdxCollType → IdxCollType)
  (emptyCol : IdxCollType)
  (shift : Nat → IdxCollType → IdxCollType)
  (thmIdxOff hypIdxOff : Nat) (thmData : CTrie (Array ThmFormat))
  (main toAdd : ModuleCacheState IdxCollType) (toAddModuleName : Name)
  : MetaM (mergeCoreData IdxCollType) := do
    mtracing
    mtrace on .zero with s!"[ModuleCacheState.mergeCore] toAddModuleName {toAddModuleName}"
    let newThmIdxOff := thmIdxOff + toAdd.thm_data.size
    let main := {main with thm_data := main.thm_data ++ toAdd.thm_data}
    let main := {main with thmNameToIdx :=
        let NthmNameToIdx := CTrie.merge (fun x _ => x) main.thmNameToIdx
          (toAdd.thmNameToIdx.map (fun x => .some (x.mapTR (· + thmIdxOff))))
        NthmNameToIdx}
    let main := {main with thmNameToHypIdx :=
        let NthmNameToHypIdx := CTrie.merge (fun x _ => x) main.thmNameToHypIdx
          (toAdd.thmNameToHypIdx.map (fun x => .some (x.mapTR (· + hypIdxOff))))
        NthmNameToHypIdx}
    let main := {main with stdBackPaIn :=
      let NstdBackPaIn := PaInG.merge union emptyCol main.stdBackPaIn
        (toAdd.stdBackPaIn.mapInds (fun x => shift thmIdxOff x) emptyCol)
      NstdBackPaIn}
    let newHypIdxOff := hypIdxOff + toAdd.stdForwSetTrie_idxToThmIdx.size
    let main := {main with stdForwSetTrie_idxToThmIdx :=
      let NstdForwSetTrie_idxToThmIdx :=
        main.stdForwSetTrie_idxToThmIdx ++ (toAdd.stdForwSetTrie_idxToThmIdx.map (fun x => x + thmIdxOff))
      NstdForwSetTrie_idxToThmIdx}
    let NthmData := thmData.insert (toAddModuleName.toString.toUTF8) toAdd.thm_data
    let NstdForwSetTrie := SetTriePG.mergeNoJoin union emptyCol
      main.stdForwSetTrie
      (toAdd.stdForwSetTrie.map id (fun x => shift hypIdxOff x) (fun T => T.mapInds (fun x => shift hypIdxOff x) emptyCol))
    let main := {main with stdForwSetTrie := NstdForwSetTrie}
    let NrwBackPaIn := PaInG.merge union emptyCol main.rwBackPaIn
      (toAdd.rwBackPaIn.mapInds (fun x => shift thmIdxOff x) emptyCol)
    let main := {main with rwBackPaIn := NrwBackPaIn}
    let NrwForwPaIn := PaInG.merge union emptyCol main.rwForwPaIn
      (toAdd.rwForwPaIn.mapInds (fun x => shift thmIdxOff x) emptyCol)
    let main := {main with rwForwPaIn := NrwForwPaIn}
    return ⟨newThmIdxOff, newHypIdxOff, main, NthmData⟩



@[specialize, inline]
def ModuleCacheState.mergeMain [Repr IdxCollType]
  (union : IdxCollType → IdxCollType → IdxCollType)
  (emptyCol : IdxCollType)
  (shift : Nat → IdxCollType → IdxCollType)
  (toAdd : ListProd Name (ModuleCacheState IdxCollType))
  : MetaM (mergeCoreData IdxCollType) :=
    toAdd.foldlM (⟨0,0,⟨#[], .empty, .empty, .dead, .root .dead #[], #[], .dead, .dead⟩, .empty⟩ : mergeCoreData IdxCollType)
      (fun module toAdd Main => do
        ModuleCacheState.mergeCore
          union emptyCol shift
          Main.thmIdxOff Main.hypIdxOff Main.thmData Main.data toAdd module
        )


@[specialize, inline]
unsafe def loadCacheData_forTest [Repr IdxCollType]
  (union : IdxCollType → IdxCollType → IdxCollType)
  (emptyCol : IdxCollType)
  (shift : Nat → IdxCollType → IdxCollType)
  (moduleNames : Array Name)
  (k : mergeCoreData IdxCollType → MetaM String) : MetaM Unit := do
    stdWithUnpickleTracingMulti' (ModuleCacheState IdxCollType) moduleNames LeanGrow.mkCacheName
      <| fun data => do
        let res ← ModuleCacheState.mergeMain
          union emptyCol shift data
        k res


unsafe def loadCacheDataS_forTest
  (moduleNames : Array Name)
  (k : mergeCoreData UInt32Array → MetaM String) : MetaM Unit := do
    loadCacheData_forTest
      UInt32Array.union UInt32Array.empty (fun x y => y.shiftAdd x.toUInt32)
      moduleNames
      (fun res => do -- will help with pretty printing
        res.thmData.foldM () (fun _ d S => do
              for t in d do
                t.mctx.loadNoCo
              return S
          )
        k res)
