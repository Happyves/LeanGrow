
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Core.Embedding.EmbedProcessForw
import LeanGrow.Src.Core.Embedding.EmbedQueryForwRW
import LeanGrow.Src.Core.Embedding.EmbedProcessForwRW
import LeanGrow.Src.Core.Induction.Detection
import LeanGrow.Src.Search.API.ScoreCore

open Lean Meta

-- # Std

#check embedForwInterMain



def embedForwInterMainS (l1 : LocalContext)
  (st : SearchState UInt32Array) :=
  @embedForwInterMain UInt32Array st.thmData _
    (fun x y z => x.foldl y (fun i s => z i.toNat s))
    (fun x y z => x.foldlM y (fun i s => z i.toNat s))
    UInt32Array.inter UInt32Array.union UInt32Array.diff
    UInt32Array.isEmpty UInt32Array.empty UInt32Array.subsetOf
    st.stdForwSetTrie_idxToSinkIdx st.thm_data
    st.stdForwSetTrie_idxToThmIdx st.thmNameToHypIdx
    st.uNodes l1 st.introTree
    st.stdForwSetTrie


#check 1

-- #exit



def addForwCandOfStdStep (l1 : LocalContext) (l2 : LocalInstances) (cfg : SearchConfig UInt32Array)
  (st : SearchState UInt32Array) : MetaM (Prod3 (SearchState UInt32Array) LocalContext LocalInstances) :=
  do
  mtracing
  if st.stdForwTimer > 0
  then
    mtrace on .one with s!"[addForwCandOfStdStep] timer at {st.stdForwTimer}, skipping"
    let st := {st with stdForwTimer := st.stdForwTimer - 1}
    return .mk st l1 l2
  else
    let rawCand ← embedForwInterMainS l1 st
    mtrace on .one with s!"[addForwCandOfStdStep] found {← rawCand.foldlM ListProd.nil (fun _ x _ y z => return .cons x (((repr y.thm.name), ← y.embedSofar.mapM ppExpr)) z)}"
    let cand ← embedForwInterPostProcess' l1 rawCand
    mtrace on .one with s!"[addForwCandOfStdStep] post processed to {← cand.foldlM ListProd.nil (fun x _ y z => return .cons (← ppExpr x) y z)}"
    cand.foldlMcps (.mk (.nil : ListProd6 Nat ForwCandData Nat ScoreType (thmGenDataEntry UInt32Array) (List (SetTrieP (Nat × Nat) UInt32Array PaIn))) st.id_gen_cand l1 l2 : Prod4 _ _ _ _) (fun term _ ugInds (.mk R igc l1 l2) q => do
      let head := term.getAppFn
      let ugInds := ugInds.foldl (fun r i => r.oInsert i.toUInt32) UInt32Array.empty
      match head with
      | .fvar ⟨.num _ i⟩ =>
          let .mk x y l1 l2 ← addForwCandidate l1 l2 cfg st cfg.sandboxMode igc R term ugInds (.inr i) .other
          q <| .mk y x l1 l2
      | .const n .. =>
          let .mk x y l1 l2 ← addForwCandidate l1 l2 cfg st cfg.sandboxMode igc R term ugInds (.inl n) (.std n.toString)
          q <| .mk y x l1 l2
      | _ => panic s!"[addForwCandOfStdStep] forward term with head other then fvar or const: {← ppExpr head}"
      ) <| fun (.mk cand igc l1 l2) => do
        mtrace on .one with s!"[addForwCandOfStdStep] adding candidates {← cand.foldlM ListProd4.nil (fun v x y z _ _ w => return .cons v (← ppExpr x.term) y (repr z) w)}"
        let st := {st with stdForwTimer := cfg.stdForwPeriod, id_gen_cand := igc, forwCandScores := cand.append st.forwCandScores, }
        return .mk st l1 l2


#check PaInG.embedForwRWMain

-- #exit

def embedForwRWMainS (l1 : LocalContext) (l2 : LocalInstances)
  (st : SearchState UInt32Array)
  (constr : UInt32Array) (revCountMax : Nat) (extWorkas : List FVarId) (E : Expr)
  (T : PaInG UInt32Array)
  : MetaM (Prod4 UInt32Array (ListProd Nat (ListProd embedForwRWData rwDirs)) LocalContext LocalInstances) :=
  PaInG.embedForwRWMain
    st.thmData UInt32Array.isEmpty UInt32Array.inter UInt32Array.union UInt32Array.diff
    UInt32Array.empty (fun x y z => x.foldl y (fun i s => z i.toNat s))
    l1 l2 constr .empty revCountMax extWorkas E T

#check 1


def addForwCandOfRW (l1 : LocalContext) (l2 : LocalInstances) (cfg : SearchConfig UInt32Array) (st : SearchState UInt32Array)
  (target_forw_id : Nat) (target_forw_type : Expr)
  : MetaM (Prod3 (SearchState UInt32Array) LocalContext LocalInstances) :=
  do
  mtracing
  match target_forw_type with
  | .forallE .. | .letE .. =>
    return .mk st l1 l2
  | _ =>
    if target_forw_type.isEq || target_forw_type.iff?.isSome
    then
      return .mk st l1 l2
    else
      -- ↑ is a attempted optimization, as in the backward case ; though there is no redundancy here
      -- these rewrites were often useless, for example getting `a = a` out of rw-ing `a = b` on itself
      let ugn := if st.uNodes.binSearchContains target_forw_id (· < ·) then unode target_forw_id else gnode target_forw_id
      let ugFv := Expr.fvar ⟨ugn⟩
      let .mk _ rawCand l1 l2 ← embedForwRWMainS l1 l2
        st st.rwForwPaIn.getIndicesS cfg.revCountMax [] target_forw_type st.rwForwPaIn
      mtrace on .one with s!"[addForwCandOfRW] found {← rawCand.foldlM ListProd.nil (fun x y z => let thmN := (repr st.thm_data[x]!.name) ; y.foldlM z (fun emb _ w => return .cons thmN (← emb.ln.foldlM ListProd.nil (fun a b c => return .cons a (← ppExpr b) c)) w))}"
      rawCand.foldlMcps (.mk (.nil : ListProd6 Nat ForwCandData Nat ScoreType (thmGenDataEntry UInt32Array) (List (SetTrieP (Nat × Nat) UInt32Array PaIn))) st.id_gen_cand l1 l2 : Prod4 _ _ _ _) (fun thmI embs (.mk cand igc l1 l2) q0 => do
        let thm := st.thm_data[thmI]!
        mtrace on .zero with s!"[addForwCandOfRW] for thm {repr thm.name}"
        embs.foldlMcps (.mk cand igc l1 l2) (fun emb dirs (.mk cand igc l1 l2) q1 => do
          mtrace on .zero with s!"[addForwCandOfRW] for embedding {← emb.ln.foldlM ListProd.nil (fun a b c => return .cons a (← ppExpr b) c)}"
          embedForwRWProcess l1 l2 thm emb
            (do mtrace on .zero with s!"[addForwCandOfRW] embedForwRWProcess failed" ; q1 (.mk cand igc l1 l2))
            (fun term ugInds => do
              mtrace on .zero with s!"[addForwCandOfRW] success with term {← ppExpr term} and {ugInds}"
              let head := term.getAppFn
              let kind : Name ⊕ Nat :=
                match head with
                | .fvar ⟨.num _ i⟩ => (.inr i)
                | .const n .. => (.inl n)
                | _ => @panic _ ⟨.inr 0⟩ s!"[addForwCandOfRW] forward rw term with head other then fvar or const: {head}"
              let ugInds := ugInds.foldl (fun r i => r.oInsert i.toUInt32) UInt32Array.empty
              let introAdmissible := st.introTree.forwIdsFromforwId
                UInt32Array.isEmpty UInt32Array.union UInt32Array.diff
                UInt32Array.empty ugInds
              embedForwRWPreIntegrate
                (fun i => introAdmissible.oContains i.toUInt32)
                st.depsCache cfg.sinkRevCutOff l1 l2 dirs target_forw_type thm ugFv term
                (fun l1 l2 => do
                  mtrace on .zero with s!"[addForwCandOfRW] embedForwRWPreIntegrate failed on rewrite of {ugFv} of type {← ppExpr target_forw_type} under equality {← ppExpr <| ← inferType term}"
                  q1 (.mk cand igc l1 l2))
                <| fun term l1 l2 => do
                  mtrace on .zero with s!"[addForwCandOfRW] success with final term {← ppExpr term}"
                  let .mk x y l1 l2 ← addForwCandidate l1 l2 cfg st cfg.sandboxMode igc cand term ugInds kind (match kind with | .inl n => .std n.toString | _ => .other)
                  q1 (.mk y x l1 l2)
              )
          ) q0
        ) <| fun (.mk cand igc l1 l2) => do
          mtrace on .one with s!"[addForwCandOfRW] adding candidates {← cand.foldlM ListProd4.nil (fun v x y z _ _ w => return .cons v (← ppExpr x.term) y (repr z) w)}"
          let st := {st with id_gen_cand := igc, forwCandScores := cand.append st.forwCandScores}
          return .mk st l1 l2

#check 1
-- #exit

def integrateForwardFull (l1 : LocalContext) (l2 : LocalInstances) (cfg : SearchConfig UInt32Array) (st : SearchState UInt32Array)
  (data : ForwCandData)
  : MetaM (Prod3 (SearchState UInt32Array) LocalContext LocalInstances) :=
  do
  mtracing
  let .mk fid fv fe st l1 l2 ← integrateForwardStd l1 l2
    cfg.revCountMax data.md data.term data.UGinds st
  mtrace on .one with s!"[integrateForwardFull] adding to cycleAddForw {fid} with type {← ppExpr fe}"
  let st := {st with cycleAddForw := .cons fid fv fe st.cycleAddForw}
  return .mk st l1 l2
