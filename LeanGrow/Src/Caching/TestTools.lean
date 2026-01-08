
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrowBeta.Caching.Load
import LeanGrowBeta.Caching.NonStrucIndunction

open Lean Meta



unsafe def exploreCaches_ThmHypInds
  (mergeOpt : Bool)
  (moduleNames : Array Name)
  : MetaM Unit := do
    loadCacheDataS_forTest mergeOpt  moduleNames <| fun data => do
      return s!"thmIdxOff : {data.thmIdxOff} ; hypIdxOff : {data.hypIdxOff}"


unsafe def exploreCaches_thmIndsOfThm
  (mergeOpt : Bool)
  (moduleNames : Array Name)
  (theo : String)
  : MetaM Unit := do
    loadCacheDataS_forTest mergeOpt  moduleNames <| fun data => do
      match data.data.thmNameToIdx.find? theo.toUTF8 with
      | .none => throwError s!"Theorem {theo} has no entry"
      | .some inds => return s!"{inds}"

unsafe def exploreCaches_hypIndsOfThm
  (mergeOpt : Bool)
  (moduleNames : Array Name)
  (theo : String)
  : MetaM Unit := do
    loadCacheDataS_forTest mergeOpt  moduleNames <| fun data => do
      match data.data.thmNameToHypIdx.find? theo.toUTF8 with
      | .none => throwError s!"Theorem {theo} has no entry"
      | .some inds => return s!"{inds}"



unsafe def exploreCaches_ThmForThmFormat
  (mergeOpt : Bool)
  (moduleNames : Array Name)
  (module : String) (thmIdx : Nat)
  (act : ThmFormat → MetaM String)
  : MetaM Unit := do
    loadCacheDataS_forTest mergeOpt  moduleNames <| fun data => do
      match data.thmData.find? module.toUTF8 with
      | .none => throwError s!"Module {module} has no entry"
      | .some thmFs =>
          let msg ← act (thmFs[thmIdx]!)
          return msg

unsafe def exploreCaches_ThmForThmFormat'
  (mergeOpt : Bool)
  (moduleNames : Array Name)
  (theo : String)
  (act : ThmFormat → MetaM String)
  : MetaM Unit :=
    loadCacheDataS_forTest mergeOpt  moduleNames <| fun data => do
      match data.data.thmNameToIdx.find? theo.toUTF8 with
      | .none => throwError s!"Theorem {theo} has no entry"
      | .some inds =>
          mtrace on .zero with s!"[exploreCaches_ThmForThmFormat'] inds {inds}"
          let idx := inds.head!
          let msg ← act (data.data.thm_data[idx]!)
          return msg


unsafe def exploreCaches_stdBackPaIn
  (mergeOpt : Bool)
  (moduleNames : Array Name)
  (act : PaIn (List Nat) → MetaM String)
  : MetaM Unit := do
    loadCacheDataS_forTest mergeOpt  moduleNames <| fun data => do
        act data.data.stdBackPaIn

unsafe def exploreCaches_rwBackPaIn
  (mergeOpt : Bool)
  (moduleNames : Array Name)
  (act : PaIn (List Nat) → MetaM String)
  : MetaM Unit := do
    loadCacheDataS_forTest mergeOpt  moduleNames <| fun data => do
        act data.data.rwBackPaIn

unsafe def exploreCaches_rwForwPaIn
  (mergeOpt : Bool)
  (moduleNames : Array Name)
  (act : PaIn (List Nat) → MetaM String)
  : MetaM Unit := do
    loadCacheDataS_forTest mergeOpt  moduleNames <| fun data => do
        act data.data.rwForwPaIn


unsafe def exploreCaches_stdForwSetTrie
  (mergeOpt : Bool)
  (moduleNames : Array Name)
  (act : SetTrie ThmFormat (PaIn (List Nat)) → MetaM String)
  : MetaM Unit := do
    loadCacheDataS_forTest mergeOpt  moduleNames <| fun data => do
        act data.data.stdForwSetTrie


unsafe def exploreCaches_stdForwSetTrie_pp
  (mergeOpt : Bool)
  (moduleNames : Array Name)
  : MetaM Unit := do
    loadCacheDataS_forTest mergeOpt  moduleNames <| fun data => do
        SetTrie.pp 0
          (fun T => do T.pp (← getLCtx) (← getLocalInstances) [] 0 (List.orderedIntersect) List.isEmpty)
          (fun thm => return s!"{repr thm.name}")
          data.data.stdForwSetTrie



def MCtxData.loadAll  (datas : List MCtxData) : MetaM Unit := do
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
  (mergeOpt : Bool)
  (moduleNames : Array Name)
  (act : PaIn (List Nat) → MetaM String)
  : MetaM Unit := do
    loadCacheDataS_forTest mergeOpt  moduleNames <| fun data => do
        let inds := data.data.stdBackPaIn.getIndices [] (List.orderedUnion)
        for i in inds do
          let thm := data.data.thm_data[i]!
          thm.mctx.load
        act data.data.stdBackPaIn

unsafe def exploreCaches_stdBackPaIn_pp'
  (mergeOpt : Bool)
  (moduleNames : Array Name)
  (act : PaIn (List Nat) → MetaM String)
  : MetaM Unit := do
    loadCacheDataS_forTest mergeOpt  moduleNames <| fun data => do
        let inds := data.data.stdBackPaIn.getIndices [] (List.orderedUnion)
        let thmsMCs := inds.mapTRR (fun i => data.data.thm_data[i]!.mctx)
        MCtxData.loadAll thmsMCs
        act data.data.stdBackPaIn


unsafe def exploreCaches_stdBackPaIn_pp''
  (mergeOpt : Bool)
  (moduleNames : Array Name)
  (act : PaIn (List Nat) → MetaM String)
  : MetaM Unit := do
    loadCacheDataS_forTest mergeOpt  moduleNames <| fun data => do
        let inds := data.data.stdBackPaIn.getIndices [] (List.orderedUnion)
        match (inds.mapTRR (fun i => data.data.thm_data[i]!.mctx)).find? (fun d => !d.decls.isEmpty) with
        | .none => throwError "hmmm"
        | .some thmsMCs =>
            thmsMCs.load'
            act data.data.stdBackPaIn



def MCtxData.load'' (data : MCtxData) : MetaM Unit := do
  -- modifyMCtx (fun mc => {mc with lDepth := data.lDepth.foldl (fun R (i, j) => R.insert i j) mc.lDepth})
  modifyMCtx (fun mc =>  {mc with userNames := data.userNames.foldl (fun R (i, j) => R.insert i j) mc.userNames})
  -- for (i, j) in data.decls do
  --   let _ ← mkMvarStdWiCoE i.name j.type

unsafe def exploreCaches_thmIndsOfThm'
  (mergeOpt : Bool)
  (moduleNames : Array Name)
  (theo : String)
  : MetaM Unit := do
    loadCacheDataS_forTest mergeOpt  moduleNames <| fun data => do
      match data.data.thmNameToIdx.find? theo.toUTF8 with
      | .none => throwError s!"Theorem {theo} has no entry"
      | .some inds =>
          let thmF := data.data.thm_data[inds.head!]!
          -- thmF.mctx.load''
          IO.println s!"thm : {repr thmF.name}\nloaded {inds}\nldepth {repr thmF.mctx.lDepth}\nuser {repr thmF.mctx.userNames}\nDecls {repr <| thmF.mctx.decls.map (fun (x,y) => (x,y.type))}"
          IO.println s!"{repr (thmF.mctx.lDepth[0]!).1}"
          -- Lean.Name.mkNum (Lean.Name.mkNum `Mathlib.Data.List.Dedup 9) 0
          -- modifyMCtx (fun mc => {mc with lDepth := mc.lDepth.insert ⟨Lean.Name.mkNum (Lean.Name.mkNum `Mathlib.Data.List.Dedup 9) 0⟩  0 })
          let lid := (thmF.mctx.lDepth[0]!).1
          modifyMCtx (fun mc => {mc with lDepth := mc.lDepth.insert lid 0 })
          -- modifyMCtx (fun mc => {mc with lDepth := mc.lDepth.insert (thmF.mctx.lDepth[0]!).1  0 })
          -- modifyMCtx (fun mc => {mc with lDepth := (thmF.mctx.lDepth.take 1).foldl (fun R (i, j) => R.insert i j) mc.lDepth})
          if ((thmF.mctx.lDepth[0]!).2 == 0)
          then
            IO.println "yes"
          -- for d in (← getMCtx).decls do
          --   IO.println s!"Hello {repr d.1}"
          -- for (i, j) in thmF.mctx.decls do
          --   IO.println s!"Hello {repr j.type}"
            -- let _ ← mkMvarStdWiCoE i.name j.type
          return "done"
          -- return s!"loaded {inds}\nDecls {repr <| (← getMCtx).decls.toArray.map (fun (x,y) => (x,y.type))}"
