
/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Caching.Query.Build
import LeanGrow.Src.Caching.Query.Load

import LeanGrow.Src.Core.Embedding.EmbedQueryBack
import LeanGrow.Src.Core.Embedding.EmbedQueryForwInclude
import LeanGrow.Src.Core.Embedding.EmbedQueryForwSimple

import LeanGrow.Src.Utils.LeanGrow.TestTools
import LeanGrow.Src.Caching.Query.Sandbox


#check PaInG.embedForwSimpleMainNoLoad
#check PaInG.embedForwSimpleMainWiLoad
#check PaInG.embedForwIncludeCore
#check PaInG.embedBackMain


-- #exit


#check 1

def PaInG.embedForwIncludeCoreS (thmData : CTrie (Array ThmFormat)) :=
  PaInG.embedForwIncludeCore thmData
    UInt32Array.inter UInt32Array.diff UInt32Array.isEmpty

#check 1

def PaInG.embedBackMainS (l1 : Lean.LocalContext) (l2 : Lean.LocalInstances)
  (thmData : CTrie (Array ThmFormat)) :=
    PaInG.embedBackMain l1 l2 thmData UInt32Array.isEmpty
      UInt32Array.inter UInt32Array.union UInt32Array.diff UInt32Array.empty


#check 1


def PaInG.embedForwInterCoreS (thmData : CTrie (Array ThmFormat)) :=
  PaInG.embedForwInterCore thmData
    UInt32Array.inter UInt32Array.diff UInt32Array.isEmpty

#check 1
open Lean Meta
-- #exit

def testSandbox_embedForwIncludeCoreS (thms : Array Name)  : Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array DepCache → Array (FVarId × List FVarId) → MetaM Unit
  | guT, gu, tT, t, lT, l, wsT, ws, ewsT, ews, Ts, deps, wdeps =>
    inSandboxS thms <| fun thmData data => do
      let mut AthmDloc := []
      for thm in thms do
        let .some thmDloc := data.thmNameToIdx.find? thm.toString.toUTF8 | throwError "Not found in data ..."
        AthmDloc := thmDloc ++ thmDloc
      let mut L := PaInG.dead
      let mut idx := 0
      for loc in AthmDloc do
        let thmD := data.thm_data[loc]!
        thmD.mctx.loadNoCo
        IO.println s!"\nLooking at {thmD.name}"
        for s in thmD.sinks do
          let h := thmD.hyps[s]!
          let htype ← withTransparency .reducible <| reduce (skipTypes := false) h.type
          IO.println s!"Adding with idx {idx} hyp {← ppExpr htype}"
          let .mk res l1 l2 ← L.insert (← getLCtx) (← getLocalInstances) htype idx
            UInt32Array.empty (fun x => UInt32Array.single x.toUInt32) (fun x y => y.oInsert x.toUInt32)
          L := res
          idx := idx + 1
      let mut Q := PaInG.dead
      idx := 0
      IO.println s!"\nBuilding ltx"
      for T in guT do
        let T ← withTransparency .reducible <| reduce (skipTypes := false) T
        IO.println s!"Adding with idx {idx} type {← ppExpr T}"
        let .mk res l1 l2 ← Q.insert (← getLCtx) (← getLocalInstances) T idx
          UInt32Array.empty (fun x => UInt32Array.single x.toUInt32) (fun x y => y.oInsert x.toUInt32)
        Q := res
        idx := idx + 1
      let res ← PaInG.embedForwIncludeCoreS thmData (← getLCtx) (← getLocalInstances) Q L
      for (i1,i2,i3,i4) in res.toListOfProd do
        IO.println s!"\nMatch (ltx) {i1} (hyps) {i2} with:\nLevels"
        for (p,l) in i4.toListOfProd do
          IO.println s!"pos {p} : {l}"
        IO.println s!"Hyps"
        for (p,e) in i3.toListOfProd do
          IO.println s!"pos {p} : {← ppExpr e}"


#check 1

def testSandbox_embedForwInterCoreS (thms : Array Name)  : Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array DepCache → Array (FVarId × List FVarId) → MetaM Unit
  | guT, gu, tT, t, lT, l, wsT, ws, ewsT, ews, Ts, deps, wdeps =>
    inSandboxS thms <| fun thmData data => do
      let mut AthmDloc := []
      for thm in thms do
        let .some thmDloc := data.thmNameToIdx.find? thm.toString.toUTF8 | throwError "Not found in data ..."
        AthmDloc := thmDloc ++ thmDloc
      let mut L := PaInG.dead
      let mut idx := 0
      for loc in AthmDloc do
        let thmD := data.thm_data[loc]!
        thmD.mctx.loadNoCo
        IO.println s!"\nLooking at {thmD.name}"
        for s in thmD.sinks do
          let h := thmD.hyps[s]!
          let htype ← withTransparency .reducible <| reduce (skipTypes := false) h.type
          IO.println s!"Adding with idx {idx} hyp {← ppExpr htype}"
          let .mk res l1 l2 ← L.insert (← getLCtx) (← getLocalInstances) htype idx
            UInt32Array.empty (fun x => UInt32Array.single x.toUInt32) (fun x y => y.oInsert x.toUInt32)
          L := res
          idx := idx + 1
      let mut Q := PaInG.dead
      idx := 0
      IO.println s!"\nBuilding ltx"
      for T in guT do
        let T ← withTransparency .reducible <| reduce (skipTypes := false) T
        IO.println s!"Adding with idx {idx} type {← ppExpr T}"
        let .mk res l1 l2 ← Q.insert (← getLCtx) (← getLocalInstances) T idx
          UInt32Array.empty (fun x => UInt32Array.single x.toUInt32) (fun x y => y.oInsert x.toUInt32)
        Q := res
        idx := idx + 1
      let res ← PaInG.embedForwInterCoreS thmData (← getLCtx) (← getLocalInstances) Q L
      for (i1,i2,i3,i4) in res.toListOfProd do
        IO.println s!"\nMatch (ltx) {i1} (hyps) {i2} with:\nLevels"
        for (p,l) in i4.toListOfProd do
          IO.println s!"pos {p} : {l}"
        IO.println s!"Hyps"
        for (p,e) in i3.toListOfProd do
          IO.println s!"pos {p} : {← ppExpr e}"


#check 1


def testSandbox_embedBackMainS (thms : Array Name)  : Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array DepCache → Array (FVarId × List FVarId) → MetaM Unit
  | guT, gu, tT, t, lT, l, wsT, ws, ewsT, ews, Ts, deps, wdeps =>
    inSandboxS thms <| fun thmData data => do
      let que ← withTransparency .reducible <| reduce (skipTypes := false) Ts[0]!
      IO.println s!"Query : {← ppExpr que}"
      IO.println s!"Searching:\n{← data.stdBackPaIn.ppS (← getLCtx) (← getLocalInstances) [] 0}\n"
      let .mk status inds res _ _ ← PaInG.embedBackMainS (← getLCtx) (← getLocalInstances) thmData
        (data.stdBackPaIn.getIndicesS) 2 [] que data.stdBackPaIn
      IO.println s!"Status {status}\nInds {inds}"
      for (is,da) in res.toListOfProd do
        IO.println s!"\nMatch {is}:\nLevels"
        for (p,l) in da.llv.toListOfProd do
          IO.println s!"\npos {p} : {l}"
        IO.println s!"\nHyps"
        for (p,e) in da.ln.toListOfProd do
          IO.println s!"\npos {p} : {← ppExpr e}"
        IO.println s!"\nT-Levels"
        for (i,p,l) in da.tlv.toListOfProd do
          IO.println s!"\nidx {i} pos {p} : {l}"
        IO.println s!"\nTnodes"
        for (i,p,e) in da.tn.toListOfProd do
          IO.println s!"\nidx {i} pos {p} : {← ppExpr e}"


#check 1


unsafe def testLoad_embedForwIncludeCoreS (moduleNames : Array Name) : Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array DepCache → Array (FVarId × List FVarId) → MetaM Unit
  | guT, gu, tT, t, lT, l, wsT, ws, ewsT, ews, Ts, deps, wdeps =>
    loadCacheDataS_forTest moduleNames <| fun data => do
      let mut out := ""
      let mut Q := PaInG.dead
      let mut idx := 0
      out := out ++ s!"\nBuilding ltx"
      for T in guT do
        let T ← withTransparency .reducible <| reduce (skipTypes := false) T
        out := out ++ s!"Adding with idx {idx} type {← ppExpr T}"
        let .mk res l1 l2 ← Q.insert (← getLCtx) (← getLocalInstances) T idx
          UInt32Array.empty (fun x => UInt32Array.single x.toUInt32) (fun x y => y.oInsert x.toUInt32)
        Q := res
        idx := idx + 1
      for thm in data.thmData.toList.foldl #[] (fun _ x y => x ++ y) do
        match thm with
        | .rw .. => continue --avoid duplicates
        | _ =>
          let mut L := PaInG.dead
          idx := 0
          for s in thm.sinks do
            let .mk res l1 l2 ← L.insert (← getLCtx) (← getLocalInstances) (thm.hyps[s]!.type) idx
              UInt32Array.empty (fun x => UInt32Array.single x.toUInt32) (fun x y => y.oInsert x.toUInt32)
            L := res
            idx := idx + 1
          let res ← PaInG.embedForwIncludeCoreS data.thmData (← getLCtx) (← getLocalInstances) Q L
          match res with
          | .nil => continue
          | _ =>
            out := out ++ s!"\n\nThm: {thm.name}"
            for (i1,i2,i3,i4) in res.toListOfProd do
              out := out ++ s!"\nMatch (ltx) {i1} (hyps) {i2} with:\nLevels"
              for (p,l) in i4.toListOfProd do
                out := out ++ s!"\npos {p} : {l}"
              out := out ++ s!"\nHyps"
              for (p,e) in i3.toListOfProd do
                out := out ++ s!"\npos {p} : {← ppExpr e}"
            out := out ++ s!"\n\nSearched in L:\n{← L.ppS (← getLCtx) (← getLocalInstances) [] 0}"
      return out


#check 1


unsafe def testLoad_embedForwInterCoreS (moduleNames : Array Name) : Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array DepCache → Array (FVarId × List FVarId) → MetaM Unit
  | guT, gu, tT, t, lT, l, wsT, ws, ewsT, ews, Ts, deps, wdeps =>
    loadCacheDataS_forTest moduleNames <| fun data => do
      let mut out := ""
      let L :=
        match data.data.stdForwSetTrie with
        | .root P _ => P
        | _ => panic! "bad settrie"
      let mut Q := PaInG.dead
      let mut idx := 0
      out := out ++ s!"\nBuilding ltx"
      for T in guT do
        let T ← withTransparency .reducible <| reduce (skipTypes := false) T
        out := out ++ s!"Adding with idx {idx} type {← ppExpr T}"
        let .mk res l1 l2 ← Q.insert (← getLCtx) (← getLocalInstances) T idx
          UInt32Array.empty (fun x => UInt32Array.single x.toUInt32) (fun x y => y.oInsert x.toUInt32)
        Q := res
        idx := idx + 1
      let res ← PaInG.embedForwInterCoreS data.thmData (← getLCtx) (← getLocalInstances) Q L
      for (i1,i2,i3,i4) in res.toListOfProd do
        let thmN := i2.foldl [] (fun i Ts =>
          let thmI := data.data.stdForwSetTrie_idxToThmIdx[i.toNat]!
          data.data.thm_data[thmI]!.name :: Ts)
        let sinkIds := i2.foldl [] (fun i Ts =>
          let thmI := data.data.stdForwSetTrie_idxToSinkIdx[i.toNat]!
          (i.toNat, thmI) :: Ts)
        out := out ++ s!"\nMatch (ltx) {i1} (hyps) {i2} with:\nThms: {thmN}\nIndex to sink pairs:{sinkIds}\nLevels"
        for (p,l) in i4.toListOfProd do
          out := out ++ s!"\npos {p} : {l}"
        out := out ++ s!"\nHyps"
        for (p,e) in i3.toListOfProd do
          out := out ++ s!"\npos {p} : {← ppExpr e}"
      out := out ++ s!"\n\nSearched in L:\n{← L.ppS (← getLCtx) (← getLocalInstances) [] 0}"
      return out


#check 1
-- #exit

unsafe def testLoad_embedBackMainS (moduleNames : Array Name)  : Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array DepCache → Array (FVarId × List FVarId) → MetaM Unit
  | guT, gu, tT, t, lT, l, wsT, ws, ewsT, ews, Ts, deps, wdeps =>
    loadCacheDataS_forTest moduleNames <| fun data => do
      let mut out := ""
      let que ← withTransparency .reducible <| reduce (skipTypes := false) Ts[0]!
      out := out ++  s!"Query : {← ppExpr que}"
      let .mk status inds res _ _ ← PaInG.embedBackMainS (← getLCtx) (← getLocalInstances) data.thmData
        (data.data.stdBackPaIn.getIndicesS) 2 [] que data.data.stdBackPaIn
      out := out ++  s!"\nStatus {status}\nInds {inds}"
      for (is,da) in res.toListOfProd do
        let thmN := is.foldl [] (fun i L => data.data.thm_data[i.toNat]!.name :: L)
        out := out ++  s!"\nMatch {is}:\nCorresponding: {thmN}\nLevels"
        for (p,l) in da.llv.toListOfProd do
          out := out ++  s!"\npos {p} : {l}"
        out := out ++  s!"\nHyps"
        for (p,e) in da.ln.toListOfProd do
          out := out ++  s!"\npos {p} : {← ppExpr e}"
        out := out ++ s!"\nT-Levels"
        for (i,p,l) in da.tlv.toListOfProd do
          out := out ++ s!"\nidx {i} pos {p} : {l}"
        out := out ++ s!"\nTnodes"
        for (i,p,e) in da.tn.toListOfProd do
          out := out ++ s!"\nidx {i} pos {p} : {← ppExpr e}"


      return out
