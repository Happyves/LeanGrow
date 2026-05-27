/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Search.Frontend.OutOfFuel
import LeanGrow.Src.Search.Frontend.Initialize


open Lean Meta Elab Tactic Term


-- **NEW** load score cache mvars at query time


def originalSearchState
  (cfg : SearchConfig UInt32Array)
  (thm_data : Array ThmFormat)
  (thmData : CTrie (Array ThmFormat))
  (stdBackPaIn : PaInG UInt32Array)
  (stdForwSetTrie : SetTrieP ThmFormat UInt32Array PaInG)
  (stdForwSetTrie_idxToThmIdx : Array Nat)
  (rwBackPaIn : PaInG UInt32Array)
  (rwForwPaIn : PaInG UInt32Array)
  (thmNameToHypIdx : CTrie UInt32Array)
  (stdForwSetTrie_idxToSinkIdx : Array Nat)
  (thmNameToThmIdx : CTrie UInt32Array)
  (G : Expr)
  : MetaM (Prod3 (SearchState UInt32Array) LocalContext LocalInstances) :=
  do
  mtracing
  let .mk P l1 l2 ← PaInG.insertS {} {} .dead G 0
  mtrace on .zero with s!"[originalSearchState] made goal PaIn"
  let st :=
    {
      id_gen_goal := 1
      cycleAddForw := .nil
      cycleAddBack := .cons 0 G .nil
      backTree := .ofGoal 0 0 G .empty .empty []
      introTree := .node {} (.mk #[0]) .empty P .dead .nil
      uNodes := #[]
      goalSpawn := #[.none]
      unif_assign := #[]
      unif_claches := .nil
      depsCache := #[]
      thm_data := thm_data
      thmData := thmData
      stdBackPaIn := stdBackPaIn
      stdForwSetTrie := stdForwSetTrie
      stdForwSetTrie_idxToThmIdx := stdForwSetTrie_idxToThmIdx
      rwBackPaIn := rwBackPaIn
      rwForwPaIn := rwForwPaIn
      thmNameToHypIdx := thmNameToHypIdx
      stdForwSetTrie_idxToSinkIdx := stdForwSetTrie_idxToSinkIdx
      thmNameToThmIdx := thmNameToThmIdx
      ugnodeToThmIdx := {}
      thmIdxToUGnode := {}
      id_gen_cand := 0
      backCandScores := .nil
      forwCandScores := .nil
      inductCandScores := .nil
      forwHeights := #[]
      goalHeights := #[1]
      forwDepths := #[]
      backDepths := #[⟨1,.nil,.none⟩]
      forwMetadata := #[]
      tacticSupportData := {linarithCooldown := cfg.tacticSupportData.linarithCooldown, ccCooldown := cfg.tacticSupportData.ccCooldown}
      statisticsAndTraces := default
    }
  let .mk nIs nGs st l1 l2 ← integrateInitialGoal l1 l2
    cfg.revCountMax 0 G st
  mtrace on .one with s!"[originalSearchState] adding to cycleAddBack : {← nGs.foldlM ListProd.nil (fun x y z => return .cons x (← ppExpr y) z)}"
  mtrace on .one with s!"[originalSearchState] adding to cycleAddForw : {← nIs.foldlM ListProd.nil (fun x _ y z => return .cons x (← ppExpr y) z)}"
  let st := {st with cycleAddForw := nIs.append st.cycleAddForw, cycleAddBack := nGs.append st.cycleAddBack}
  return .mk st l1 l2





#check 1
#check MetavarContext.eAssignment


partial def overflowToGetStacktrace (n : Nat) : Nat := 1 + overflowToGetStacktrace (n+1)
  -- without the + 1 it gets optimised to an infinite loop


def printMetaDeclsA : MetaM String := do
  let mctx ← getMCtx
  let lvls := mctx.lDepth.toList
  let pl := "Levels\n" ++ (String.intercalate "\n" (lvls.map (fun x => s!"{repr x}")))
  let mvs := mctx.decls.toList.map (fun (x,y) => (x,y.type))
  let inter ← mvs.mapM (fun (x,y) => return s!"{repr x} : {← ppExpr y}")
  let pmv := "Mvars\n" ++ (String.intercalate "\n" ( pl :: inter))
  let assign := mctx.eAssignment.toList
  let pa := "Assignements\n" ++ (String.intercalate "\n" (← assign.mapM (fun (x,y) => return s!"{repr x} : { y}")))
  return pmv ++ "\n" ++ pa

#check MetavarDecl

def _root_.Lean.MVarId.revertAll' (mvarId : MVarId) : MetaM (Array FVarId × MVarId) := mvarId.withContext do
  mvarId.checkNotAssigned `revertAll
  let mut toRevert := #[]
  for fvarId in (← getLCtx).getFVarIds do
    unless (← fvarId.getDecl).isAuxDecl do
      toRevert := toRevert.push fvarId
  mvarId.setKind .natural
  mvarId.revert toRevert
    (preserveOrder := true)
    (clearAuxDeclsInsteadOfRevert := true)

def Lean.MetavarContext.setExprMVarLCtx (mctx : MetavarContext) (mvarId : MVarId)
    (l1 : LocalContext) (l2 : LocalInstances)  : MetavarContext :=
  mctx.modifyExprMVarDecl mvarId fun mdecl => { mdecl with lctx := l1, localInstances := l2 }


def Lean.MVarId.setLCtx [MonadMCtx m] (mvarId : MVarId)
    (l1 : LocalContext) (l2 : LocalInstances) : m Unit :=
  modifyMCtx (·.setExprMVarLCtx mvarId l1 l2)


def printForwDecls (st : SearchState UInt32Array) : MetaM String := do
  let mut res := ""
  for i in List.range st.id_gen_forw do
    let n : FVarId := .mk <| if st.uNodes.contains i then unode i else gnode i
    match ← n.getDecl with
    | .cdecl _ _ _ T .. =>
      res := res ++ s!"{n.name} : {← ppExpr T}\n"
    | .ldecl _ _ _ T V .. =>
      res := res ++ s!"{n.name} : {← ppExpr T} :=\n  {← ppExpr V}\n"
  return res




def growImpl
  (msgRef : Syntax)
  (fuel : Nat)
  (cfg : SearchConfig UInt32Array)
  (thm_data : Array ThmFormat)
  (thmData : CTrie (Array ThmFormat))
  (stdBackPaIn : PaInG UInt32Array)
  (stdForwSetTrie : SetTrieP ThmFormat UInt32Array PaInG)
  (stdForwSetTrie_idxToThmIdx : Array Nat)
  (rwBackPaIn : PaInG UInt32Array)
  (rwForwPaIn : PaInG UInt32Array)
  (thmNameToHypIdx : CTrie UInt32Array)
  (stdForwSetTrie_idxToSinkIdx : Array Nat)
  (thmNameToThmIdx : CTrie UInt32Array)
  : TacticM Unit :=
  do
  mtracing
  withMainContext do
    withSynthesize do
      liftMetaTactic <| fun g => do
        -- dbg_trace s!"Goal: {repr g}"
        let (_, G) ← g.revertAll'
        -- dbg_trace s!"Goal: {repr G}"
        -- let test ← isDefEq (← instantiateMVars <| .mvar g) (mkAppN (← instantiateMVars <| .mvar G) (revs.map Expr.fvar))
        -- dbg_trace s!"Test: {test}"
        let mctx ← getMCtx
        let GT ← G.getType
        -- dbg_trace ← printMetaDeclsA
        mtrace on .zero with s!"[growImpl] reverted goal type {← ppExpr GT}"
        let .mk st l1 l2 ← originalSearchState
          cfg thm_data thmData stdBackPaIn stdForwSetTrie stdForwSetTrie_idxToThmIdx
          rwBackPaIn rwForwPaIn thmNameToHypIdx stdForwSetTrie_idxToSinkIdx thmNameToThmIdx GT
        mtrace on .zero with s!"[growImpl] Initial state:"
        mtrace on .zero with s!"[growImpl] introTree: {st.introTree.pp 0}"
        mtrace on .zero with s!"[growImpl] backTree: {← st.backTree.pp 0}"
        let .mk st solutions l1 l2 ← searchCore l1 l2 cfg st fuel
        withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
          match solutions with
          | .nil =>
              mtrace on .one with s!"[growImpl] Out of fuel"
              mtrace on .one with s!"[growImpl] Final state:"
              mtrace on .one with s!"[growImpl] introTree: {st.introTree.pp 0}"
              mtrace on .one with s!"[growImpl] backTree: {← st.backTree.pp 0}"
              growOutOfFuel msgRef GT st
              let term ← mkSorry GT true
              mtrace on .zero with s!"[growImpl] search completed"
              setMCtx mctx
              -- let test ← isDefEq (← instantiateMVars <| .mvar g) (mkAppN (← instantiateMVars <| .mvar G) (revs.map Expr.fvar))
              -- dbg_trace s!"Test: {test}"
              G.setLCtx l1 l2
              let _ ← isDefEq (← instantiateMVars <| .mvar G) term
              G.assign term
              mtrace on .zero with s!"[growImpl] mvar assigned"
              return []
          | .cons term _ _ =>
              mtrace on .zero with s!"[growImpl] found solution {← ppExpr term}"
              mtrace on .three with s!"[growImpl] raw {term}"
              mtrace on .one with s!"[growImpl] Final state:"
              mtrace on .one with s!"[growImpl] introTree: {st.introTree.pp 0}"
              mtrace on .one with s!"[growImpl] forward decls:\n{← printForwDecls st}"
              mtrace on .one with s!"[growImpl] backTree: {← st.backTree.pp 0}"
              mtrace on .zero with s!"[growImpl] search completed"
              setMCtx mctx -- have to restore because calls to clearAssignements in grow clear those of the tactic framework
              -- let test ← isDefEq (← instantiateMVars <| .mvar g) (mkAppN (← instantiateMVars <| .mvar G) (revs.map Expr.fvar))
              -- dbg_trace s!"Test: {test}"
              G.setLCtx l1 l2
              match Kernel.check (← getEnv) l1 term with
              | .ok _ =>
                  let _ ← isDefEq (← instantiateMVars <| .mvar G) term
                  G.assign term
                  -- dbg_trace s!"sanity: {sanity}"
                  mtrace on .zero with s!"[growImpl] mvar assigned"
                  -- dbg_trace ← printMetaDeclsA
                  return []
              | .error er =>
                  match er with
                  | .declHasFVars _ name ert =>
                      throwError s!"[Grow] kernel throws free variable error for term:\nname : {name}\nterm pp: {← PpExpr ert l1 l2}\n term raw: {repr ert}"
                  | _ =>
                      throwError (er.toMessageData (← getOptions)) ++ s!"\n\n[Grow] raw term:\n{repr term}"



#check sorryAx
#check 1
#check Tactic.closeMainGoal


#check Tactic.evalRevert
#check instantiateMVars
#check MVarId.modifyLCtx



open Term

#check MVarId.withReverted
#check Kernel.check
