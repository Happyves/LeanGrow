
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

open Lean Meta

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
        IO.println s!"\nLooking at {thmD.name}"
        for s in thmD.sinks do
          let h := thmD.hyps[s]!
          IO.println s!"Adding with idx {idx} hyp {← ppExpr h.type}"
          let .mk res l1 l2 ← L.insert (← getLCtx) (← getLocalInstances) h.type idx
            UInt32Array.empty (fun x => UInt32Array.single x.toUInt32) (fun x y => y.oInsert x.toUInt32)
          L := res
          idx := idx + 1
      let mut Q := PaInG.dead
      idx := 0
      IO.println s!"\nBuilding ltx"
      for T in guT do
        IO.println s!"Adding with idx {idx} type {← ppExpr T}"
        let .mk res l1 l2 ← L.insert (← getLCtx) (← getLocalInstances) T idx
          UInt32Array.empty (fun x => UInt32Array.single x.toUInt32) (fun x y => y.oInsert x.toUInt32)
        L := res
        idx := idx + 1
      let res ← PaInG.embedForwIncludeCoreS thmData (← getLCtx) (← getLocalInstances) Q L
      for (i1,i2,i3,i4) in res.toListOfProd do
        IO.println s!"\nMatch {i1} {i2} with:\nLevels"
        for (p,l) in i4.toListOfProd do
          IO.println s!"\npos {p} : {l}"
        IO.println s!"\nHyps"
        for (p,e) in i3.toListOfProd do
          IO.println s!"\npos {p} : {← ppExpr e}"


#check 1


def testSandbox_embedBackMainS (thms : Array Name)  : Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array DepCache → Array (FVarId × List FVarId) → MetaM Unit
  | guT, gu, tT, t, lT, l, wsT, ws, ewsT, ews, Ts, deps, wdeps =>
    inSandboxS thms <| fun thmData data => do
      IO.println s!"Searching:\n{← data.stdBackPaIn.ppS (← getLCtx) (← getLocalInstances) [] 0}\n"
      let .mk status inds res _ _ ← PaInG.embedBackMainS (← getLCtx) (← getLocalInstances) thmData
        (data.stdBackPaIn.getIndicesS) 2 [] Ts[0]! data.stdBackPaIn
      IO.println s!"Status {status}\nInds {inds}"
      for (is,da) in res.toListOfProd do
        IO.println s!"\nMatch {is}:\nLevels"
        for (p,l) in da.llv.toListOfProd do
          IO.println s!"\npos {p} : {l}"
        IO.println s!"\nHyps"
        for (p,e) in da.ln.toListOfProd do
          IO.println s!"\npos {p} : {← ppExpr e}"
