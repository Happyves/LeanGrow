
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrowAlpha.Final.Search.TacticSupport.SupportAPI
import LeanGrowAlpha.Final.Search.TacticSupport.InjectivityNoConfusion

open Lean Meta Mathlib.Meta.FunProp

open private Mathlib.Meta.FunProp.emptyDischarge from Mathlib.Tactic.FunProp.Elab


def funPropMirror
  (target_goal_id : Nat) (target_goal_type : Expr)
  (CFG : SearchConfig) (st : SearchState (List Nat))
  {α : Sort _} (k : SearchState (List Nat) → MetaM α) : MetaM α :=
    trace set Tracing.Flags.none in do
    -- mirror `Mathlib.Meta.FunProp.funPropTac`
    withReducible <| forallTelescopeReducing (← whnfR target_goal_type) fun _ type => do
      match ← getFunProp? type with
      | .none =>
          mtrace on .zero with s!"[funPropMirror] irrelevant for fun prop"
          withDefault <| k st
      | .some .. =>
          let cfg :  Mathlib.Meta.FunProp.Config := {}
          let disch := Mathlib.Meta.FunProp.emptyDischarge
          let namesToUnfold : Array Name := #[]
          let namesToUnfold := namesToUnfold.append defaultNamesToUnfold
          let ctx : Mathlib.Meta.FunProp.Context :=
            { config := cfg,
              disch := disch
              constToUnfold := .ofArray namesToUnfold _}
          onGoalOnly
            target_goal_id target_goal_type CFG st
            (fun goal => do
              mtrace on .zero with s!"[funPropMirror] trying fun prop"
              let (r?, _) ← funProp target_goal_type ctx |>.run {}
              if let .some r := r?
              then
                goal.assign r.proof
                return true
              else
                return false
              ) "FunProp"  <| fun newI newG st => do
                  withDefault <| k {st with cycleAddForw := newI.append st.cycleAddForw, cycleAddBack := newG.append st.cycleAddBack}


def Lean.Expr.ineqIsh (e : Expr) : MetaM Bool := do
  match e.le? with
  | some .. => return true
  | none =>
  match e.lt? with
  | some .. => return true
  | none => return false

def Lean.Expr.eqIsh (e : Expr) : MetaM Bool := do
  match e.eq? with
  | some .. => return true
  | none =>
  match e.ne? with
  | some .. => return true
  | none => return false

def linarithNormNum
  (target_goal_id : Nat)
  (cfg : SearchConfig) (st : SearchState (List Nat))
  (ctx : Meta.Context) (state : Meta.State) (mvid : MVarId)
  {α : Sort _} (k : SearchState (List Nat) → MetaM α) : MetaM α :=
  trace set Tracing.Flags.none in
  onGoalOnly' target_goal_id cfg st ctx state mvid
    (fun mvid => do
      mtrace on .zero with s!"[linarithNormNum] trying norm num"
      let simpctx ← mkSimpContext
      let res ← Mathlib.Meta.NormNum.normNumAt mvid simpctx #[]
      return res.isSome)
    "normNumGoal"
    <| fun newI newG st => do
      let st := {st with cycleAddForw := newI.append st.cycleAddForw, cycleAddBack := newG.append st.cycleAddBack}
      if st.tacticSupportData.linarithCooldown == 0
      then
        onGoalOnly' target_goal_id cfg st ctx state mvid
          (fun mv => do
              mtrace on .zero with s!"[linarithNormNum] trying linarith"
              Linarith.linarith false [] {} mv ; return true)
          "linarithGoal"
          <| fun newI newG st => do
            let st := {st with tacticSupportData := {st.tacticSupportData with linarithCooldown := cfg.tacticSupportData.linarithCooldown}}
            k {st with cycleAddForw := newI.append st.cycleAddForw, cycleAddBack := newG.append st.cycleAddBack}
      else
        mtrace on .zero with s!"[linarithNormNum] linarith skip, cooldown {st.tacticSupportData.linarithCooldown}"
        let st := {st with tacticSupportData := {st.tacticSupportData with linarithCooldown := st.tacticSupportData.linarithCooldown - 1}}
        k st



def ccLinarithNormNum
  (target_goal_id : Nat)
  (cfg : SearchConfig) (st : SearchState (List Nat))
  (ctx : Meta.Context) (state : Meta.State) (mvid : MVarId)
  {α : Sort _} (k : SearchState (List Nat) → MetaM α) : MetaM α :=
  trace set Tracing.Flags.none in do
  if st.tacticSupportData.ccCooldown == 0
  then
    onGoalOnly' target_goal_id cfg st ctx state mvid
      (fun mv => do
        mtrace on .zero with s!"[ccLinarithNormNum] trying cc"
        mv.cc ; return true)
      "ccGoal"
      <| fun newI newG st => do
        let st := {st with tacticSupportData := {st.tacticSupportData with linarithCooldown := cfg.tacticSupportData.linarithCooldown}}
        let st := {st with cycleAddForw := newI.append st.cycleAddForw, cycleAddBack := newG.append st.cycleAddBack}
        linarithNormNum target_goal_id cfg st ctx state mvid k
  else
    mtrace on .zero with s!"[ccLinarithNormNum] cc skip, cooldown {st.tacticSupportData.ccCooldown}"
    let st := {st with tacticSupportData := {st.tacticSupportData with linarithCooldown := st.tacticSupportData.linarithCooldown - 1}}
    linarithNormNum target_goal_id cfg st ctx state mvid k


open Mathlib.Tactic Mathlib.Tactic.Module Mathlib.Tactic.Ring

def moduleMirror (g : MVarId) : MetaM Unit := do
  let l ← matchScalars g
  discard <| l.mapM fun mvar ↦ AtomM.run .instances (Ring.proveEq mvar)

#check MVarId.congrN!
#check MVarId.gcongr



def supportOnGoal
  (target_goal_id : Nat) (target_goal_type : Expr)
  (cfg : SearchConfig) (st : SearchState (List Nat))
  {α : Sort _} (k : SearchState (List Nat) → MetaM α) : MetaM α :=
  trace set Tracing.Flags.none in do
  match target_goal_type with
  | .app N? rhs =>
      match N? with
      | .const N?? _ =>
          if N?? == `Not
          then
            let e ← whnfR rhs
            if ← e.ineqIsh
            then
              let ugis := st.introTree.gatherUGidsToGoalId target_goal_id []
              let ⟨ctx,state,mvid⟩ ← prepareSandboxContext st ugis target_goal_type
              linarithNormNum target_goal_id cfg st ctx state mvid k
            else
              if ← e.eqIsh
              then
                let ugis := st.introTree.gatherUGidsToGoalId target_goal_id []
                let ⟨ctx,state,mvid⟩ ← prepareSandboxContext st ugis target_goal_type
                ccLinarithNormNum target_goal_id cfg st ctx state mvid k
              else
                funPropMirror target_goal_id target_goal_type cfg st k
          else
            funPropMirror target_goal_id target_goal_type cfg st k
      | .app rel _ =>
          let .const rel _ := rel.getAppFn | funPropMirror target_goal_id target_goal_type cfg st k
          if rel == `Eq
          then
            let ugis := st.introTree.gatherUGidsToGoalId target_goal_id []
            let ⟨ctx,state,mvid⟩ ← prepareSandboxContext st ugis target_goal_type
            onGoalOnly'
              target_goal_id cfg st ctx state mvid
              (fun mvid => do
                mtrace on .zero with s!"[supportOnGoal] trying congr 1"
                let _ ← mvid.congrN! (.some 1)
                return true)
              "congrGoal 1"
              <| fun newI newG st => do
                let st := {st with cycleAddForw := newI.append st.cycleAddForw, cycleAddBack := newG.append st.cycleAddBack}
                onGoalOnly'
                  target_goal_id cfg st ctx state mvid
                  (fun mvid => do
                    mtrace on .zero with s!"[supportOnGoal] trying congr 2"
                    let _ ← mvid.congrN! (.some 2)
                    return true)
                  "congrGoal 2"
                  <| fun newI newG st => do
                    let st := {st with cycleAddForw := newI.append st.cycleAddForw, cycleAddBack := newG.append st.cycleAddBack}
                    onGoalOnly'
                      target_goal_id cfg st ctx state mvid
                      (fun mv => do
                          mtrace on .zero with s!"[supportOnGoal] trying moduele"
                          moduleMirror mv ; return true)
                      "moduleGoal"
                      <| fun newI newG st => do
                        let st := {st with cycleAddForw := newI.append st.cycleAddForw, cycleAddBack := newG.append st.cycleAddBack}
                        onGoalOnly'
                          target_goal_id cfg st ctx state mvid
                          (fun mv => do
                              mtrace on .zero with s!"[supportOnGoal] trying ring"
                              AtomM.run .reducible (proveEq mv) ; return true)
                          "ringGoal"
                          <| fun newI newG st => do
                            let st := {st with cycleAddForw := newI.append st.cycleAddForw, cycleAddBack := newG.append st.cycleAddBack}
                            ccLinarithNormNum target_goal_id cfg st ctx state mvid k
          else
            if rel == `Ne
            then
              let ugis := st.introTree.gatherUGidsToGoalId target_goal_id []
              let ⟨ctx,state,mvid⟩ ← prepareSandboxContext st ugis target_goal_type
              ccLinarithNormNum target_goal_id cfg st ctx state mvid k
            else
              if rel == ``LE.le || rel == ``LT.lt
              then
                let ugis := st.introTree.gatherUGidsToGoalId target_goal_id []
                let ⟨ctx,state,mvid⟩ ← prepareSandboxContext st ugis target_goal_type
                onGoalOnly'
                  target_goal_id cfg st ctx state mvid
                  (fun mvid => do
                    mtrace on .zero with s!"[supportOnGoal] trying gcongr"
                    let (pass?,_,_) ← mvid.gcongr .none []
                    return pass?)
                  "gcongrGoal"
                  <| fun newI newG st => do
                    let st := {st with cycleAddForw := newI.append st.cycleAddForw, cycleAddBack := newG.append st.cycleAddBack}
                    linarithNormNum target_goal_id cfg st ctx state mvid k
              else
                funPropMirror target_goal_id target_goal_type cfg st k
      | _ => funPropMirror target_goal_id target_goal_type cfg st k
  | _ => funPropMirror target_goal_id target_goal_type cfg st k

#check Not
#check Ne
#check Eq
#check LE.le

def absurdOrLeave
  (target_forw_id : Nat) (posType : Expr)
  (revCountMax : Nat) (st : SearchState (List Nat))
  {α : Sort _} (k : SearchState (List Nat) → MetaM α) : MetaM α :=
  trace set Tracing.Flags.none in do
  let ltx ← st.introTree.mergeLtxForForwIds id (List.orderedUnion (· ≤ ·)) [target_forw_id] .dead
  ltx.findS ltx.getIndicesS revCountMax posType
    (k st) (fun _ => k st) (fun _ => k st)
    <| fun res => do
      match res with
      | [] =>
          mtrace on .zero with s!"[absurdOrLeave] found no positive occurence {← ppExpr posType}"
          k st
      | h :: _ =>
          let ugnPos := if st.uNodes.binSearchContains h (· < ·) then unode h else gnode h
          mtrace on .zero with s!"[absurdOrLeave] found positive occurence at {ugnPos}"
          let (goalI,goalE) := st.introTree.topGoalForForwId target_forw_id
          mtrace on .zero with s!"[absurdOrLeave] targeting top-most goal {goalI}"
          let ugn := if st.uNodes.binSearchContains target_forw_id (· < ·) then unode target_forw_id else gnode target_forw_id
          let term ← mkAbsurd goalE (.fvar ⟨ugnPos⟩) (.fvar ⟨ugn⟩)
          mtrace on .zero with s!"[absurdOrLeave] integrating"
          integrateBackwardStd
            revCountMax goalI term (.string s!"[Absurd] forw {target_forw_id} goal {goalI}") 0 .nil .nil st
            <| fun newI newG st => do
              let st := {st with cycleAddForw := newI.append st.cycleAddForw, cycleAddBack := newG.append st.cycleAddBack}
              k st


def ccLinarith
  (target_goal_id : Nat)
  (cfg : SearchConfig) (st : SearchState (List Nat))
  (ctx : Meta.Context) (state : Meta.State) (mvid : MVarId)
  {α : Sort _} (k : SearchState (List Nat) → MetaM α) : MetaM α :=
  trace set Tracing.Flags.none in do
  if st.tacticSupportData.ccCooldown == 0
  then
    onGoalOnly' target_goal_id cfg st ctx state mvid
      (fun mv => do
        mtrace on .zero with s!"[ccLinarith] trying cc"
        mv.cc ; return true)
      "ccGoal"
      <| fun newI newG st => do
        let st := {st with tacticSupportData := {st.tacticSupportData with linarithCooldown := cfg.tacticSupportData.linarithCooldown}}
        let st := {st with cycleAddForw := newI.append st.cycleAddForw, cycleAddBack := newG.append st.cycleAddBack}
        if st.tacticSupportData.linarithCooldown == 0
        then
          onGoalOnly' target_goal_id cfg st ctx state mvid
            (fun mv => do
                mtrace on .zero with s!"[ccLinarith] trying linarith"
                Linarith.linarith false [] {} mv ; return true)
            "linarithGoal"
            <| fun newI newG st => do
              let st := {st with tacticSupportData := {st.tacticSupportData with linarithCooldown := cfg.tacticSupportData.linarithCooldown}}
              k {st with cycleAddForw := newI.append st.cycleAddForw, cycleAddBack := newG.append st.cycleAddBack}
        else
          mtrace on .zero with s!"[ccLinarith] skiped linarith with cooldown {st.tacticSupportData.linarithCooldown}"
          let st := {st with tacticSupportData := {st.tacticSupportData with linarithCooldown := st.tacticSupportData.linarithCooldown - 1}}
          k st
  else
    mtrace on .zero with s!"[ccLinarith] skiped cc with cooldown {st.tacticSupportData.ccCooldown}"
    let st := {st with tacticSupportData := {st.tacticSupportData with ccCooldown := st.tacticSupportData.ccCooldown - 1}}
    if st.tacticSupportData.linarithCooldown == 0
    then
      onGoalOnly' target_goal_id cfg st ctx state mvid
        (fun mv => do Linarith.linarith false [] {} mv ; return true)
        "linarithGoal"
        <| fun newI newG st => do
          mtrace on .zero with s!"[ccLinarith] trying linarith"
          let st := {st with tacticSupportData := {st.tacticSupportData with linarithCooldown := cfg.tacticSupportData.linarithCooldown}}
          k {st with cycleAddForw := newI.append st.cycleAddForw, cycleAddBack := newG.append st.cycleAddBack}
    else
      mtrace on .zero with s!"[ccLinarith] skiped linarith with cooldown {st.tacticSupportData.linarithCooldown}"
      let st := {st with tacticSupportData := {st.tacticSupportData with linarithCooldown := st.tacticSupportData.linarithCooldown - 1}}
      k st




def supportOnForw
  (target_forw_id : Nat) (target_forw_type : Expr)
  (cfg : SearchConfig) (st : SearchState (List Nat))
  {α : Sort _} (k : SearchState (List Nat) → MetaM α) : MetaM α :=
  trace set Tracing.Flags.none in do
  match target_forw_type with
  | .app N? rhs =>
      match N? with
      | .const N?? _ =>
          if N?? == `Not
          then
            let e ← whnfR rhs
            if ← e.ineqIsh
            then
              let (goalI,goalE) := st.introTree.topGoalForForwId target_forw_id
              let ugis := st.introTree.gatherUGidsToGoalId goalI []
              let ⟨ctx,state,mvid⟩ ← prepareSandboxContext st ugis goalE
              if st.tacticSupportData.linarithCooldown == 0
              then
                onGoalOnly' goalI cfg st ctx state mvid
                  (fun mv => do
                      mtrace on .zero with s!"[supportOnForw] trying linarith"
                      Linarith.linarith false [] {} mv ; return true)
                  "linarithGoal"
                  <| fun newI newG st => do
                    let st := {st with tacticSupportData := {st.tacticSupportData with linarithCooldown := cfg.tacticSupportData.linarithCooldown}}
                    k {st with cycleAddForw := newI.append st.cycleAddForw, cycleAddBack := newG.append st.cycleAddBack}
              else
                mtrace on .zero with s!"[ccLinarith] skiped linarith with cooldown {st.tacticSupportData.linarithCooldown}"
                let st := {st with tacticSupportData := {st.tacticSupportData with linarithCooldown := st.tacticSupportData.linarithCooldown - 1}}
                k st
            else
              absurdOrLeave
                target_forw_id rhs cfg.revCountMax st k
          else
            k st
      | .app rel _ =>
          let .const rel _ := rel.getAppFn | k st
          if rel == `Eq
          then
            let ug := if st.uNodes.binSearchContains target_forw_id (· < ·) then unode target_forw_id else gnode target_forw_id
            let (goalI,goalE) := st.introTree.topGoalForForwId target_forw_id
            let fvis ← goalE.getFvarIdsRec []
            let mut ltx : LocalContext := {}
            for fvid in fvis do
              let dec ← fvid.getDecl
              ltx := ltx.addDecl dec
            let ctx : Meta.Context :=  {lctx := ltx}
            let mvid ← mkFreshMVarId
            let mctx : MetavarContext := {}
            let mctx := mctx.addExprMVarDecl mvid `onGoalStrictly ltx {} goalE
            let state : Meta.State := {mctx := mctx}
            onGoalStrictly' goalI cfg st ctx state mvid
              (fun mvid => do
                  mtrace on .zero with s!"[supportOnForw] trying acyclic"
                  mvid.acyclic (.fvar ⟨ug⟩))
              "acyclic"
              <| fun p1 newI newG st => do
                let st := {st with cycleAddForw := newI.append st.cycleAddForw, cycleAddBack := newG.append st.cycleAddBack}
                injectivityOrNoConfusionOrLeave
                  target_forw_id target_forw_type goalI goalE cfg.revCountMax st
                  <| fun p2 newI newG st => do
                    let st := {st with cycleAddForw := newI.append st.cycleAddForw, cycleAddBack := newG.append st.cycleAddBack}
                    onGoalStrictly' goalI cfg st ctx state mvid
                      (fun mvid => do
                        mtrace on .zero with s!"[supportOnForw] trying cases for no-confusion"
                        let res ← mvid.cases ⟨ug⟩
                        return res.isEmpty)
                      "noConfusionIndicesCore"
                      <| fun p3 newI newG st => do
                        let st := {st with cycleAddForw := newI.append st.cycleAddForw, cycleAddBack := newG.append st.cycleAddBack}
                        if p1 || p2 || p3
                        then
                          k st
                        else
                          let ugis := st.introTree.gatherUGidsToGoalId goalI []
                          let ⟨ctx,state,mvid⟩ ← prepareSandboxContext st ugis goalE
                          ccLinarith goalI cfg st ctx state mvid k
          else
            if rel == `Ne
            then
              let (goalI,goalE) := st.introTree.topGoalForForwId target_forw_id
              let ugis := st.introTree.gatherUGidsToGoalId goalI []
              let ⟨ctx,state,mvid⟩ ← prepareSandboxContext st ugis goalE
              ccLinarith goalI cfg st ctx state mvid k
            else
              if rel == ``LE.le || rel == ``LT.lt
              then
                let (goalI,goalE) := st.introTree.topGoalForForwId target_forw_id
                let ugis := st.introTree.gatherUGidsToGoalId goalI []
                let ⟨ctx,state,mvid⟩ ← prepareSandboxContext st ugis goalE
                if st.tacticSupportData.linarithCooldown == 0
                then
                  onGoalOnly' goalI cfg st ctx state mvid
                    (fun mv => do
                      mtrace on .zero with s!"[supportOnForw] trying linarith"
                      Linarith.linarith false [] {} mv ; return true)
                    "linarithGoal"
                    <| fun newI newG st => do
                      let st := {st with tacticSupportData := {st.tacticSupportData with linarithCooldown := cfg.tacticSupportData.linarithCooldown}}
                      k {st with cycleAddForw := newI.append st.cycleAddForw, cycleAddBack := newG.append st.cycleAddBack}
                else
                  mtrace on .zero with s!"[ccLinarith] skiped linarith with cooldown {st.tacticSupportData.linarithCooldown}"
                  let st := {st with tacticSupportData := {st.tacticSupportData with linarithCooldown := st.tacticSupportData.linarithCooldown - 1}}
                  k st
              else
                k st
      | _ => k st
  | _ =>
      if target_forw_type.isFalse -- no reductions ...
      then
        let (goalI,goalE) := st.introTree.topGoalForForwId target_forw_id
        mtrace on .zero with s!"[supportOnForw] exfalso availble for goal {goalI}"
        let ugn := if st.uNodes.binSearchContains target_forw_id (· < ·) then unode target_forw_id else gnode target_forw_id
        let term ← mkFalseElim goalE (.fvar ⟨ugn⟩)
        integrateBackwardStd
          cfg.revCountMax goalI term (.string s!"[Exfalso] forw {target_forw_id} goal {goalI}") 0 .nil .nil st
          <| fun newI newG st => do
            let st := {st with cycleAddForw := newI.append st.cycleAddForw, cycleAddBack := newG.append st.cycleAddBack}
            k st

      else
        k st



#check 1


#check MVarId.congrN!


/-- In particular, tactics are only trie on first generation cycle-additions-/
def runTacticSupport
  (cfg : SearchConfig) (st : SearchState (List Nat))
  {α : Sort _} (k : SearchState (List Nat) → MetaM α) : MetaM α :=
  trace set Tracing.Flags.none in do
  let fwCA := st.cycleAddForw
  let bwCA := st.cycleAddBack
  fwCA.foldlMcps st (fun fid fe st q => do
    mtrace on .zero with s!"[runTacticSupport] forward {fid} {← ppExpr fe}"
    supportOnForw fid fe cfg st q) <| fun st => do
      bwCA.foldlMcps st (fun fid fe st q => do
        mtrace on .zero with s!"[runTacticSupport] backward {fid} {← ppExpr fe}"
        supportOnGoal fid fe cfg st q) k
