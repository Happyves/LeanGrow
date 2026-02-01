
/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Caching.Query.Build
import LeanGrow.Src.Caching.Query.Load

import LeanGrow.Src.Core.Embedding.EmbedQueryBackRW
import LeanGrow.Src.Core.Embedding.EmbedQueryForwRW

import LeanGrow.Src.Utils.LeanGrow.TestTools
import LeanGrow.Src.Caching.Query.Sandbox


#check PaInG.embedForwRWMain
#check embedBackRWMain

#check UInt32Array.foldl

-- #exit


#check 1

def PaInG.embedForwRWMainS (thmData : CTrie (Array ThmFormat)) :=
  PaInG.embedForwRWMain thmData UInt32Array.isEmpty
    UInt32Array.inter UInt32Array.union UInt32Array.diff
    UInt32Array.empty (fun y z f => UInt32Array.foldl y z (fun i a => f i.toNat a))

#check 1

def embedBackRWMainnS (l1 : Lean.LocalContext) (l2 : Lean.LocalInstances)
  (thmData : CTrie (Array ThmFormat)) :=
    embedBackRWMain l1 l2 thmData
      (fun y z f => UInt32Array.foldl y z (fun i a => f i.toNat a))
      UInt32Array.isEmpty UInt32Array.inter UInt32Array.union UInt32Array.diff
      UInt32Array.empty


#check 1


open Lean Meta
-- #exit

def testSandbox_embedForwRWMainS (thms : Array Name)  : Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array DepCache → Array (FVarId × List FVarId) → MetaM Unit
  | guT, gu, tT, t, lT, l, wsT, ws, ewsT, ews, Ts, deps, wdeps =>
    inSandboxS thms <| fun thmData data => do
      let que ← withTransparency .reducible <| reduce (skipTypes := false) Ts[0]!
      let .mk _ res l1 l2 ← data.rwForwPaIn.embedForwRWMainS thmData (← getLCtx) (← getLocalInstances)
        (data.rwForwPaIn.getIndicesS) UInt32Array.empty 2 [] que
      withLCtx l1 l2 <| do
        match res with
        | .nil => IO.println "Found nothing"
        | _ =>
          for (i,emb) in res.toListOfProd do
            let thmM := data.thm_data[i]!
            match thmM with
            | .std .. => continue
            | .rw tname _ _ goal rep .. =>
              IO.println s!"\nThm : {tname}\nGoal : {← ppExpr goal}\nReplacement : {← ppExpr rep}\nEmbeddings"
              for (em,dirs) in emb.toListOfProd do
                IO.println s!"Dirs {repr dirs}"
                for (p,l) in em.llv.toListOfProd do
                  IO.println s!"pos {p} : {l}"
                IO.println s!"Hyps"
                for (p,e) in em.ln.toListOfProd do
                  IO.println s!"pos {p} : {← ppExpr e}"

#check 1



def testSandbox_embedBackRWMainnS (thms : Array Name)  : Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array DepCache → Array (FVarId × List FVarId) → MetaM Unit
  | guT, gu, tT, t, lT, l, wsT, ws, ewsT, ews, Ts, deps, wdeps =>
    inSandboxS thms <| fun thmData data => do
      let que ← withTransparency .reducible <| reduce (skipTypes := false) Ts[0]!
      let .mk _ res l1 l2 ← embedBackRWMainnS (← getLCtx) (← getLocalInstances)
        thmData (data.rwBackPaIn.getIndicesS) UInt32Array.empty 2 [] que data.rwBackPaIn
      withLCtx l1 l2 <| do
        match res with
        | .nil => IO.println "Found nothing"
        | _ =>
          for (i,emb) in res.toListOfProd do
            let thmM := data.thm_data[i]!
            match thmM with
            | .std .. => continue
            | .rw tname _ _ goal rep .. =>
              IO.println s!"\nThm : {tname}\nGoal : {← ppExpr goal}\nReplacement : {← ppExpr rep}\nEmbeddings"
              for (em,dirs,_) in emb.toListOfProd do
                IO.println s!"Dirs {repr dirs}"
                for (p,l) in em.llv.toListOfProd do
                  IO.println s!"pos {p} : {l}"
                IO.println s!"Hyps"
                for (p,e) in em.ln.toListOfProd do
                  IO.println s!"pos {p} : {← ppExpr e}"
                IO.println s!"T-Levels"
                for (i,p,l) in em.tlv.toListOfProd do
                  IO.println s!"idx {i} pos {p} : {l}"
                IO.println s!"Tnodes"
                for (i,p,e) in em.tn.toListOfProd do
                  IO.println s!"idx {i} pos {p} : {← ppExpr e}"



#check 1


unsafe def testLoad_embedForwRWMainS (moduleNames : Array Name) : Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array DepCache → Array (FVarId × List FVarId) → MetaM Unit
  | guT, gu, tT, t, lT, l, wsT, ws, ewsT, ews, Ts, deps, wdeps =>
    loadCacheDataS_forTest moduleNames <| fun data => do
      let que ← withTransparency .reducible <| reduce (skipTypes := false) Ts[0]!
      let .mk _ res l1 l2 ← data.data.rwForwPaIn.embedForwRWMainS data.thmData (← getLCtx) (← getLocalInstances)
        (data.data.rwForwPaIn.getIndicesS) UInt32Array.empty 2 [] que
      withLCtx l1 l2 <| do
        match res with
        | .nil => return "Found nothing"
        | _ =>
          let mut out := ""
          for (i,emb) in res.toListOfProd do
            let thmM := data.data.thm_data[i]!
            match thmM with
            | .std .. => continue
            | .rw tname _ _ goal rep .. =>
              out := out ++ s!"\n\nThm : {tname}\nGoal : {← ppExpr goal}\nReplacement : {← ppExpr rep}\nEmbeddings"
              for (em,dirs) in emb.toListOfProd do
                out := out ++ s!"\nDirs {repr dirs}\nLevels:"
                for (p,l) in em.llv.toListOfProd do
                  out := out ++ s!"\npos {p} : {l}"
                out := out ++ s!"\nHyps"
                for (p,e) in em.ln.toListOfProd do
                  out := out ++ s!"\npos {p} : {← ppExpr e}"
          return out


#check 1
-- #exit

unsafe def testLoad_embedBackRWMainnS (moduleNames : Array Name) : Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array DepCache → Array (FVarId × List FVarId) → MetaM Unit
  | guT, gu, tT, t, lT, l, wsT, ws, ewsT, ews, Ts, deps, wdeps =>
    loadCacheDataS_forTest moduleNames <| fun data => do
      let que ← withTransparency .reducible <| reduce (skipTypes := false) Ts[0]!
      let .mk _ res l1 l2 ← embedBackRWMainnS (← getLCtx) (← getLocalInstances)
        data.thmData (data.data.rwBackPaIn.getIndicesS) UInt32Array.empty 2 [] que data.data.rwBackPaIn
      withLCtx l1 l2 <| do
        match res with
        | .nil => return "Found nothing"
        | _ =>
          let mut out := ""
          for (i,emb) in res.toListOfProd do
            let thmM := data.data.thm_data[i]!
            match thmM with
            | .std .. => continue
            | .rw tname _ _ goal rep .. =>
              out := out ++ s!"\n\nThm : {tname}\nGoal : {← ppExpr goal}\nReplacement : {← ppExpr rep}\nEmbeddings"
              for (em,dirs,_) in emb.toListOfProd do
                out := out ++ s!"\nDirs {repr dirs}\nLevels:"
                for (p,l) in em.llv.toListOfProd do
                  out := out ++ s!"\npos {p} : {l}"
                out := out ++ s!"\nHyps"
                for (p,e) in em.ln.toListOfProd do
                  out := out ++ s!"\npos {p} : {← ppExpr e}"
                out := out ++ s!"\nT-Levels"
                for (i,p,l) in em.tlv.toListOfProd do
                  out := out ++ s!"\nidx {i} pos {p} : {l}"
                out := out ++ s!"\nTnodes"
                for (i,p,e) in em.tn.toListOfProd do
                  out := out ++ s!"\nidx {i} pos {p} : {← ppExpr e}"

          return out

#check 1
