
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Core.Embedding.EmbedProcessForwAPI
import LeanGrow.Src.Core.Embedding.EmbedQueryForwRW
import LeanGrow.Src.Core.Embedding.EmbedProcessForwRW
import LeanGrow.Src.Core.Induction.Detection
import LeanGrow.Src.Search.API.ScoreCore

open Lean Meta

-- # Std



def embedForwIncludeMainS (l1 : LocalContext) (l2 : LocalInstances)
  (st : SearchState (List Nat)) :=
  @embedForwIncludeMain (List Nat) st.thmData _ id
    (fun i => let j := st.stdForwSetTrie_idxToThmIdx[i]! ; st.thm_data[j]!)
    (fun n =>
      match st.thmNameToHypIdx.find? n.toString.toUTF8 with
      | .none => []
      | .some ids => ids)
    (fun i => st.uNodes.binSearchContains i (· < · )) -- since increasing indices are pushed on it
    (List.orderedIntersect) (List.orderedUnion) (List.orderedDiff) List.isEmpty []
    l1 l2 st.introTree
    st.stdForwSetTrie


#check 1





def addForwCandOfStdStep (l1 : LocalContext) (l2 : LocalInstances) (cfg : SearchConfig)
  (st : SearchState (List Nat)) : MetaM (Prod3 (SearchState (List Nat)) LocalContext LocalInstances) :=
  do -- trace set Tracing.Flags.none in do
  if st.stdForwTimer > 0
  then
    mtrace on .one with s!"[addForwCandOfStdStep] timer at {st.stdForwTimer}, skipping"
    let st := {st with stdForwTimer := st.stdForwTimer - 1}
    return .mk st l1 l2
  else
    let rawCand ← embedForwIncludeMainS l1 l2 st
    mtrace on .one with s!"[addForwCandOfStdStep] found {← rawCand.foldlM ListProd.nil (fun x _ y z => return .cons x (((repr y.thm.name), ← y.embedSofar.mapM ppExpr)) z)}"
    let cand ← embedForwIncludePostProcess l1 l2 rawCand
    mtrace on .one with s!"[addForwCandOfStdStep] post processed to {← cand.foldlM ListProd.nil (fun x _ y z => return .cons (← ppExpr x) y z)}"
    cand.foldlMcps (.mk (ListProd6.nil : ListProd6 Nat ForwCandData Nat ScoreType (CPaIn (List Nat)) (List (CSetTrie  (List Nat) Nat))) st.id_gen_cand l1 l2 : Prod4 _ _ _ _) (fun term _ ugInds (.mk R igc l1 l2) q => do
      let head := term.getAppFn
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


#check PaIn.embedForwRWMain



def embedForwRWMainS (l1 : LocalContext) (l2 : LocalInstances)  (st : SearchState (List Nat))
  (constr : (List Nat)) (revCountMax : Nat) (extWorkas : List FVarId) (E : Expr)
  (T : PaIn (List Nat))
  : MetaM (Prod3 (ListProd Nat (ListProd embedForwRWData rwDirs)) LocalContext LocalInstances) :=
  @PaIn.embedForwRWMain (List Nat) _ _ _
    st.thmData List.isEmpty (List.orderedIntersect) (List.orderedUnion) (List.orderedDiff)
    [] id l1 l2 constr revCountMax extWorkas E T

#check 1


def addForwCandOfRW (l1 : LocalContext) (l2 : LocalInstances) (cfg : SearchConfig) (st : SearchState (List Nat))
  (target_forw_id : Nat) (target_forw_type : Expr)
  : MetaM (Prod3 (SearchState (List Nat)) LocalContext LocalInstances) :=
  do --trace set Tracing.Flags.none in do
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
      let .mk rawCand l1 l2 ← embedForwRWMainS l1 l2
        st st.rwForwPaIn.getIndicesS cfg.revCountMax [] target_forw_type st.rwForwPaIn
      mtrace on .one with s!"[addForwCandOfRW] found {← rawCand.foldlM ListProd.nil (fun x y z => let thmN := (repr st.thm_data[x]!.name) ; y.foldlM z (fun emb _ w => return .cons thmN (← emb.ln.foldlM ListProd.nil (fun a b c => return .cons a (← ppExpr b) c)) w))}"
      rawCand.foldlMcps (.mk (.nil : ListProd6 Nat ForwCandData Nat ScoreType (CPaIn (List Nat)) (List (CSetTrie (List Nat) Nat))) st.id_gen_cand l1 l2 : Prod4 _ _ _ _) (fun thmI embs (.mk cand igc l1 l2) q0 => do
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
              let introAdmissible := st.introTree.forwIdsFromforwId ugInds
              embedForwRWPreIntegrate
                (fun i => introAdmissible.orderedContains i)
                st.depsCache l1 l2 dirs target_forw_type thm ugFv term
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


-- Select

-- integrate
#check integrateForwardStd

-- update ranks

#print ForwCandData

def integrateForwardFull (l1 : LocalContext) (l2 : LocalInstances) (cfg : SearchConfig) (st : SearchState (List Nat))
  (data : ForwCandData)
  : MetaM (Prod3 (SearchState (List Nat)) LocalContext LocalInstances) :=
  do --trace set Tracing.Flags.none in do
  let .mk fid fe st l1 l2 ← integrateForwardStd l1 l2
    cfg.revCountMax data.md data.term data.UGinds st
  mtrace on .one with s!"[integrateForwardFull] adding to cycleAddForw {fid} with type {← ppExpr fe}"
  let st := {st with cycleAddForw := .cons fid fe st.cycleAddForw}
  return .mk st l1 l2
