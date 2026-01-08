
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrowBeta.Caching.Build
import LeanGrowBeta.Data.PathIndex.Indexing


open Lean Meta

variable {IdxCollType : Type _}


structure mergeCoreData (IdxCollType : Type _) where
  thmIdxOff : Nat
  hypIdxOff : Nat
  data : ModuleCacheState IdxCollType
  thmData : CTrie (Array ThmFormat)

@[specialize, inline]
def SetTrieP.mergeSpe [Repr IdxCollType]
  (l1 : LocalContext) (l2 : LocalInstances)
  (thmData : CTrie (Array ThmFormat))
  (toList : IdxCollType → List Nat)
  (insert intersect union difference : IdxCollType → IdxCollType → IdxCollType)
  (emptyCol : IdxCollType)  (empty? : IdxCollType → Bool) (size : IdxCollType → Nat)
  (main : ModuleCacheState IdxCollType)
  (snd : SetTrie ThmFormat (PaIn IdxCollType))
  (mergeOpt : Bool)
  : MetaM (ModuleCacheState IdxCollType) :=
    match main.stdForwSetTrie, snd with
    | .root cm, .root cs =>
      if mergeOpt
      then
        if cm.isEmpty
        then
          return {main with stdForwSetTrie := snd}
        else
          List.splitGreedyMergeMcps
            (PaIn.dead, PaIn.dead)
            (fun x (y,z) q => do q (PaIn.merge union emptyCol x y, ← PaIn.mergeLSpe union emptyCol l1 l2 thmData x z))
            (fun (x,y) =>
              match y.max intersect empty? size with
              | .none => .none
              | .some inds m =>
                  let res := PaIn.buildCore x [] 0 (fun x => intersect x inds) intersect empty?
                  let is := res.foldl emptyCol (fun _ i R => union i R)
                  .some (is, res) m
              )
            (fun x (is,_) q => do
              let real ← x.sharesIndicesWith intersect empty? is
              if real then q (.some ()) else q .none)
            (fun x (is,_) _ => x.deleteOfInds is difference emptyCol empty?)
            (fun x => match x.clean emptyCol empty? with | .dead => true | _ => false)
            (fun (_,es) q => do
              es.foldlMcps PaIn.dead (fun e is T q => do
                for toLoad in (toList is) do
                  let thmI := main.stdForwSetTrie_idxToThmIdx[toLoad]!
                  (main.thm_data[thmI]!).mctx.load
                let ⟨res,_,_⟩ ← PaIn.insertMulti l1 l2 e is T emptyCol insert
                q res) <| fun res => q res)
            (fun (_,es) τ q => do
              es.foldlMcps τ (fun e is T q => do
                for toLoad in (toList is) do
                  let thmI := main.stdForwSetTrie_idxToThmIdx[toLoad]!
                  (main.thm_data[thmI]!).mctx.load
                let ⟨res,_,_⟩ ← PaIn.insertMulti l1 l2 e is T emptyCol insert
                q res) <| fun res => q res)
            (cm ++ cs)
            <| fun res => do
              return {main with stdForwSetTrie := .root res}
      else
        return {main with stdForwSetTrie := .root (cm ++ cs)}
    | _, _ => throwError s!"[SetTrieP.mergeSpe] settries not in root format ?!"



@[specialize, inline]
def ModuleCacheState.mergeCore [Repr IdxCollType]
  (toList : IdxCollType → List Nat)
  (insert intersect union difference : IdxCollType → IdxCollType → IdxCollType)
  (emptyCol : IdxCollType)  (empty? : IdxCollType → Bool) (size : IdxCollType → Nat)
  (shift : Nat → IdxCollType → IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (thmIdxOff hypIdxOff : Nat) (thmData : CTrie (Array ThmFormat))
  (main toAdd : ModuleCacheState IdxCollType) (toAddModuleName : Name)
  (mergeOpt : Bool)
  : MetaM (mergeCoreData IdxCollType) := do
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
      let NstdBackPaIn := PaIn.merge union emptyCol main.stdBackPaIn
        (toAdd.stdBackPaIn.mapInds (fun x => shift thmIdxOff x) emptyCol)
      NstdBackPaIn}
    let newHypIdxOff := hypIdxOff + toAdd.stdForwSetTrie_idxToThmIdx.size
    let main := {main with stdForwSetTrie_idxToThmIdx :=
      let NstdForwSetTrie_idxToThmIdx :=
        main.stdForwSetTrie_idxToThmIdx ++ (toAdd.stdForwSetTrie_idxToThmIdx.map (fun x => x + thmIdxOff))
      NstdForwSetTrie_idxToThmIdx}
    let NthmData := thmData.insert (toAddModuleName.toString.toUTF8) toAdd.thm_data
    let main ← SetTrieP.mergeSpe l1 l2
      NthmData toList insert intersect union difference emptyCol empty? size
      main
      (toAdd.stdForwSetTrie.map (fun T => T.mapInds (fun x => shift hypIdxOff x) emptyCol) id)
      mergeOpt
    let NrwBackPaIn := PaIn.merge union emptyCol main.rwBackPaIn
      (toAdd.rwBackPaIn.mapInds (fun x => shift thmIdxOff x) emptyCol)
    let main := {main with rwBackPaIn := NrwBackPaIn}
    let NrwForwPaIn := PaIn.merge union emptyCol main.rwForwPaIn
      (toAdd.rwForwPaIn.mapInds (fun x => shift thmIdxOff x) emptyCol)
    let main := {main with rwForwPaIn := NrwForwPaIn}
    return ⟨newThmIdxOff, newHypIdxOff, main, NthmData⟩



@[specialize, inline]
def ModuleCacheState.mergeMain [Repr IdxCollType]
  (toList : IdxCollType → List Nat)
  (insert intersect union difference : IdxCollType → IdxCollType → IdxCollType)
  (emptyCol : IdxCollType)  (empty? : IdxCollType → Bool) (size : IdxCollType → Nat)
  (shift : Nat → IdxCollType → IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (toAdd : ListProd Name (ModuleCacheState IdxCollType))
  (mergeOpt : Bool)
  : MetaM (mergeCoreData IdxCollType) :=
    toAdd.foldlM (⟨0,0,⟨#[], .empty, .empty, .dead, .root [], #[], .dead, .dead⟩, .empty⟩ : mergeCoreData IdxCollType)
      (fun module toAdd Main => do
        ModuleCacheState.mergeCore
          toList insert intersect union difference emptyCol empty? size shift
          l1 l2 Main.thmIdxOff Main.hypIdxOff Main.thmData Main.data toAdd module mergeOpt
        )


@[specialize, inline]
unsafe def loadCacheData_forTest [Repr IdxCollType]
  (toList : IdxCollType → List Nat)
  (insert intersect union difference : IdxCollType → IdxCollType → IdxCollType)
  (emptyCol : IdxCollType)  (empty? : IdxCollType → Bool) (size : IdxCollType → Nat)
  (shift : Nat → IdxCollType → IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (moduleNames : Array Name)
  (mergeOpt : Bool)
  (k : mergeCoreData IdxCollType → MetaM String) : MetaM Unit := do
    stdWithUnpickleTracingMulti' (ModuleCacheState IdxCollType) moduleNames LeanGrow.mkCacheName
      <| fun data => do
        let res ← ModuleCacheState.mergeMain
          toList insert intersect union difference emptyCol empty? size shift
            l1 l2 data mergeOpt
        k res


@[specialize, inline]
unsafe def loadCacheDataS_forTest
  (mergeOpt : Bool)
  (moduleNames : Array Name)
  (k : mergeCoreData (List Nat) → MetaM String) : MetaM Unit := do
    loadCacheData_forTest
      id (List.orderedUnion) (List.orderedIntersect )
      (List.orderedUnion ) (List.orderedDiff ) [] List.isEmpty List.length
      (fun s l => l.mapTR (fun x => x+s)) --important that it preserves order
      (← getLCtx) (← getLocalInstances)
      moduleNames
      mergeOpt
      (fun res => do -- will help with pretty printing
        res.thmData.foldM () (fun _ d S => do
              for t in d do
                t.mctx.load
              return S
          )
        k res)
