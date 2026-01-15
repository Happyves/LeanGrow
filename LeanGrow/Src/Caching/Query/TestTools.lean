
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Caching.Query.Load

open Lean Meta

unsafe def exploreCaches_thms
  (moduleNames : Array Name)
  : MetaM Unit := do
    loadCacheDataS_forTest  moduleNames <| fun data => do
      return data.thmData.fold "" (fun key thmV st => st ++ s!"\nKey: {String.fromUTF8! key}\nVals : {(thmV.map (fun x => match x.name with | .inl x => x | .inr v => v.name))} \n")



unsafe def exploreCaches_ThmHypInds
  (moduleNames : Array Name)
  : MetaM Unit := do
    loadCacheDataS_forTest  moduleNames <| fun data => do
      return s!"thmIdxOff : {data.thmIdxOff} ; hypIdxOff : {data.hypIdxOff}"


unsafe def exploreCaches_thmIndsOfThm
  (moduleNames : Array Name)
  (theo : String)
  : MetaM Unit := do
    loadCacheDataS_forTest moduleNames <| fun data => do
      match data.data.thmNameToIdx.find? theo.toUTF8 with
      | .none => throwError s!"Theorem {theo} has no entry"
      | .some inds => return s!"{inds}"

unsafe def exploreCaches_hypIndsOfThm
  (moduleNames : Array Name)
  (theo : String)
  : MetaM Unit := do
    loadCacheDataS_forTest moduleNames <| fun data => do
      match data.data.thmNameToHypIdx.find? theo.toUTF8 with
      | .none => throwError s!"Theorem {theo} has no entry"
      | .some inds => return s!"{inds}"



unsafe def exploreCaches_ThmForThmFormat
  (moduleNames : Array Name)
  (module : String) (thmIdx : Nat)
  (act : ThmFormat → MetaM String)
  : MetaM Unit := do
    loadCacheDataS_forTest moduleNames <| fun data => do
      match data.thmData.find? module.toUTF8 with
      | .none => throwError s!"Module {module} has no entry"
      | .some thmFs =>
          let msg ← act (thmFs[thmIdx]!)
          return msg

unsafe def exploreCaches_ThmForThmFormat'
  (moduleNames : Array Name)
  (theo : String)
  (act : ThmFormat → MetaM String)
  : MetaM Unit :=
    loadCacheDataS_forTest moduleNames <| fun data => do
      mtracing
      match data.data.thmNameToIdx.find? theo.toUTF8 with
      | .none => throwError s!"Theorem {theo} has no entry"
      | .some inds =>
          mtrace on .zero with s!"[exploreCaches_ThmForThmFormat'] inds {inds}"
          let idx := inds.head!
          let msg ← act (data.data.thm_data[idx]!)
          return msg


unsafe def exploreCaches_stdBackPaIn
  (moduleNames : Array Name)
  (act : PaInG UInt32Array → MetaM String)
  : MetaM Unit := do
    loadCacheDataS_forTest moduleNames <| fun data => do
        act data.data.stdBackPaIn

unsafe def exploreCaches_rwBackPaIn
  (moduleNames : Array Name)
  (act : PaInG UInt32Array → MetaM String)
  : MetaM Unit := do
    loadCacheDataS_forTest moduleNames <| fun data => do
        act data.data.rwBackPaIn

unsafe def exploreCaches_rwForwPaIn
  (moduleNames : Array Name)
  (act : PaInG UInt32Array → MetaM String)
  : MetaM Unit := do
    loadCacheDataS_forTest moduleNames <| fun data => do
        act data.data.rwForwPaIn


unsafe def exploreCaches_stdForwSetTrie
  (moduleNames : Array Name)
  (act : SetTrieP ThmFormat UInt32Array PaInG → MetaM String)
  : MetaM Unit := do
    loadCacheDataS_forTest moduleNames <| fun data => do
        act data.data.stdForwSetTrie


unsafe def exploreCaches_stdForwSetTrie_pp
  (moduleNames : Array Name)
  : MetaM Unit := do
    loadCacheDataS_forTest moduleNames <| fun data => do
        SetTrieP.pp 0
          (fun T => do T.ppS (← getLCtx) (← getLocalInstances) [] 0)
          (fun thm => return s!"{repr thm.name}")
          data.data.stdForwSetTrie



def MCtxData.loadAll  (datas : Array MCtxData) : MetaM Unit := do
  let ltx ← getLCtx
  let linst ← getLocalInstances
  for data in datas do
    modifyMCtx (fun mc =>
      let mc := {mc with lDepth := data.lDepth.foldl (fun R (i, j) => R.insert i j) mc.lDepth}
      let mc := {mc with userNames := data.userNames.foldl (fun R (i, j) => R.insert i j) mc.userNames}
      let mc :=  data.decls.foldl (fun R (i, j) =>
        {R with decls := R.decls.insert i ({j with lctx := ltx, localInstances := linst, index := R.mvarCounter}), mvarCounter := R.mvarCounter + 1 }
        ) mc
      mc)


unsafe def exploreCaches_stdBackPaIn_pp
  (moduleNames : Array Name)
  : MetaM Unit := do
    loadCacheDataS_forTest moduleNames <| fun data => do
        let inds := data.data.stdBackPaIn.getIndices UInt32Array.empty UInt32Array.union
        for i in inds do
          let thm := data.data.thm_data[i.toNat]!
          thm.mctx.loadNoCo
        data.data.stdBackPaIn.ppS (← getLCtx) (← getLocalInstances) [] 0
