/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Caching.Query.Build
import LeanGrow.Src.Caching.Query.Load

import LeanGrow.Src.Core.Embedding.EmbedProcessBack
import LeanGrow.Src.Core.Embedding.EmbedProcessForwAPI
import LeanGrow.Src.Core.Embedding.TestTools_QueryStd


open Lean Meta


unsafe def testBack (moduleNames : Array Name) : Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array DepCache → Array (FVarId × List FVarId) → MetaM Unit
  | guT, gu, tT, t, lT, l, wsT, ws, ewsT, ews, Ts, deps, wdeps =>
    loadCacheDataS_forTest moduleNames <| fun data => do
      let que ← withTransparency .reducible <| reduce (skipTypes := false) Ts[0]!
      let .mk _ _ res l1 l2 ← PaInG.embedBackMainS (← getLCtx) (← getLocalInstances) data.thmData
        (data.data.stdBackPaIn.getIndicesS) 2 [] que data.data.stdBackPaIn
      let l2 := l2.cleanPatchesAndWokers
      match res with
      | .nil => return "Found nothing"
      | _ =>
        let mut out := ""
        for (inds,emb) in res.toListOfProd do
          let i := inds[0]!
          let thmM := data.data.thm_data[i.toNat]!
            let res ← embedBackProcess' l1 l2 thmM emb
            match res with
            | .none => out := out ++ s!"\n\nInstance synth fail for an embed of {thmM.name}"
            | .some _ arg_lvls todo_lvls arg_exprs todo_expr =>
              let .mk term tnodeNum l1 l2 ← embedBackPreIntegrate l1 l2
                thmM 42 arg_lvls todo_lvls arg_exprs todo_expr
              let mut inter := s!"\n\nSuccess for {thmM.name} with subgoals"
              for i in List.range tnodeNum do
                let ffv : FVarId := .mk (tnode 42 i)
                let T ← ffv.GetType l1 l2
                inter := inter ++ s!"\n{ffv.name} : {← ppExpr T}"
              inter := inter ++ s!"\nT-Level assignements "
              for (i,p,l) in emb.tlv.toListOfProd do
                inter := inter ++ s!"\nidx {i} pos {p} : {l}"
              inter := inter ++ s!"\nTnode assignemet"
              for (i,p,e) in emb.tn.toListOfProd do
                inter := inter ++ s!"\nidx {i} pos {p} : {← ppExpr e}"
              inter := inter ++ s!"\nAnd with term {← ppExpr term}"
              out := out ++ inter
        return out


#check 1

#check UInt32Array.foldlM



def embedForwInterMain_S
  (thmembedForwData : CTrie (Array ThmFormat))
  (stdForwSetTrie_idxToSinkIdx : Array Nat)
  (thm_data : Array ThmFormat) (stdForwSetTrie_idxToThmIdx : Array Nat)
  (thmNameToHypIdx : CTrie UInt32Array) (uNodes : Array Nat)
  (l1 : LocalContext)
  (Q' : IntroTree UInt32Array) (T : SetTrieP ThmFormat UInt32Array PaInG) :=
  embedForwInterMain thmembedForwData
    (fun a x f => a.foldl x (fun i s => f i.toNat s)) (fun a x f => a.foldlM x (fun i s => f i.toNat s))
    UInt32Array.inter UInt32Array.union UInt32Array.diff UInt32Array.isEmpty UInt32Array.empty
    stdForwSetTrie_idxToSinkIdx thm_data stdForwSetTrie_idxToThmIdx thmNameToHypIdx uNodes
    l1 Q' T

#check 1

inductive FakeIntroTree where
| leaf (guIds : UInt32Array)
| node (guIds : UInt32Array) (kids : List FakeIntroTree)
deriving Inhabited


def mkIntroTreOfFake (L2 : LocalInstances)
  (guT gu : Array Expr) (scafold : FakeIntroTree)
  : MetaM (UInt32Array × IntroTree UInt32Array) := do
  match scafold with
  | .leaf guIds =>
    let (.mk l2 ltx) ← guIds.foldlM (Prod.mk (#[] : LocalInstances) PaInG.dead) (fun i (.mk l2 ltx) => do
      let I := i.toNat
      let fv := gu[I]!
      let l2 := (match L2.find? (fun x => x.fvar == fv) with | .none => l2 | .some li => l2.push li)
      let .mk ltx _ _ ← ltx.insert (← getLCtx) L2 guT[I]! I
        UInt32Array.empty (fun x => UInt32Array.single x.toUInt32) (fun x y => y.oInsert x.toUInt32)
      return .mk l2 ltx
      )
    return .mk guIds <| .leaf l2 .empty guIds .dead ltx
  | .node guIds kids =>
    let res ← kids.mapM (mkIntroTreOfFake L2 guT gu)
    let (.mk l2 ltx) ← guIds.foldlM (Prod.mk (#[] : LocalInstances) PaInG.dead) (fun i (.mk l2 ltx) => do
      let I := i.toNat
      let fv := gu[I]!
      let l2 := (match L2.find? (fun x => x.fvar == fv) with | .none => l2 | .some li => l2.push li)
      let .mk ltx _ _ ← ltx.insert (← getLCtx) L2 guT[I]! I
        UInt32Array.empty (fun x => UInt32Array.single x.toUInt32) (fun x y => y.oInsert x.toUInt32)
      return .mk l2 ltx
      )
    let (alldirs,K)  := res.foldl (fun (alldirs,K) (inds,k) =>
      let alldirs := UInt32Array.union alldirs inds
      let K := .cons .empty inds k K
      (alldirs,K)
      ) (UInt32Array.empty, (ListProd3.nil : ListProd3 UInt32Array UInt32Array (IntroTree UInt32Array)))
    return .mk (UInt32Array.union alldirs guIds) <| .node l2 .empty guIds .dead ltx K


#check 1


unsafe def testForw (moduleNames : Array Name) (scafold : FakeIntroTree) : Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array DepCache → Array (FVarId × List FVarId) → MetaM Unit
  | guT, gu, tT, t, lT, l, wsT, ws, ewsT, ews, Ts, deps, wdeps =>
    loadCacheDataS_forTest moduleNames <| fun data => do
      mtracing
      let (_, IT) ← mkIntroTreOfFake (← getLocalInstances) guT gu scafold
      mtrace on .zero with s!"IT {IT.ppDirsLocInst 0}"
      let mut uNodes := #[]
      let mut i := 0
      for n in gu do
        if n.fvarId!.isUnode
        then
          uNodes := uNodes.push i
          i := i+1
        else
          i := i+1
      let res ← embedForwInterMain_S
        data.thmData data.data.stdForwSetTrie_idxToSinkIdx data.data.thm_data
        data.data.stdForwSetTrie_idxToThmIdx data.data.thmNameToHypIdx uNodes
        (← getLCtx) IT data.data.stdForwSetTrie
      let res ← embedForwInterPostProcess' (← getLCtx) res
      let mut out := ""
      for (term,_,guinds) in res.toListOfProd do
        let T ← inferType term
        out := out ++ s!"\n\nNew type : {← ppExpr T}\nTerm : {← ppExpr term}\nguinds : {guinds}"
      return out


#check 1
