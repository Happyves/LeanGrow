
/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Caching.Query.Build
import LeanGrow.Src.Caching.Query.Load

import LeanGrow.Src.Core.Embedding.EmbedProcessBack
import LeanGrow.Src.Core.Embedding.TestTools_QueryRW


#check PaInG.embedForwRWMain
#check embedBackRWMain

#check UInt32Array.foldl




open Lean Meta


#check 1
-- #exit

unsafe def testBackRw (moduleNames : Array Name) : Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array DepCache → Array (FVarId × List FVarId) → MetaM Unit
  | guT, gu, tT, t, lT, l, wsT, ws, ewsT, ews, Ts, deps, wdeps =>
    loadCacheDataS_forTest moduleNames <| fun data => do
      let que ← withTransparency .reducible <| reduce (skipTypes := false) Ts[0]!
      let .mk _ res l1 l2 ← embedBackRWMainnS (← getLCtx) (← getLocalInstances)
        data.thmData (data.data.rwBackPaIn.getIndicesS) UInt32Array.empty 2 [] que data.data.rwBackPaIn
      match res with
      | .nil => return "Found nothing"
      | _ =>
        let mut out := ""
        let mut NewBackIdx := 0
        for (i,emb) in res.toListOfProd do
          let thmM := data.data.thm_data[i]!
          for (em,dirs,ws) in emb.toListOfProd do
            let l2 := l2.cleanPatchesAndWokers
            let res ← embedBackProcess l1 l2 thmM em
            match res with
            | .none => out := out ++ s!"\n\nInstance synth fail for an embed of {thmM.name}"
            | .some _ arg_lvls todo_lvls arg_exprs todo_expr =>
                let .mk res l1 l2 ← embedBackRWPreIntegrate
                  (fun _ => true) l1 l2 deps 10 dirs NewBackIdx
                  que ws thmM arg_lvls todo_lvls arg_exprs todo_expr
                NewBackIdx := NewBackIdx + 1
                match res with
                | .none => out := out ++ s!"\n\nRewrite fail for an emb of {thmM.name}"
                | .some term tnodeNum =>
                    let mut inter := s!"\n\nSuccess for {thmM.name} with subgoals"
                    for i in List.range tnodeNum do
                      let ffv : FVarId := .mk (tnode (NewBackIdx - 1) i)
                      let T ← ffv.GetType l1 l2
                      inter := inter ++ s!"\n{ffv.name} : {← ppExpr T}"
                    inter := inter ++ s!"\nAnd with term {← ppExpr term}"
                    out := out ++ inter
        return out

#check 1


#exit


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
