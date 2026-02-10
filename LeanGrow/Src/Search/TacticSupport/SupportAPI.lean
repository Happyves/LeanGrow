
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrowAlpha.Final.Search.API.IntegrateForw
import LeanGrowAlpha.Final.Search.API.IntegrateBack

import Mathlib.Tactic

open Lean Meta


/--
Keeps tnodes as fvars ...
-/
partial def prepareSandboxContext
  (st : SearchState (List Nat))
  (coherentUGinds : List Nat) (goal_type : Expr)
  : MetaM (Prod3 Context State MVarId) :=
  trace set Tracing.Flags.none in
  let rec help (goal_type : Expr) (ltx : LocalContext) (seen : List FVarId) : MetaM (LocalContext × List FVarId) :=
    goal_type.onAllSubtermsFoldNoPartialM (ltx, seen) (fun e (ltx, seen) => do
      match e with
      | .fvar x@⟨.num (.num kind _) _⟩ =>
          if kind == `t
          then
            if seen.contains x
            then
              return (ltx, seen)
            else
              let dec ← x.getDecl
              let (ltx,seen) ← help goal_type ltx seen
              mtrace on .zero with s!"[prepareSandboxContext] adding {repr x} of type {← ppExpr dec.type}"
              return (ltx.addDecl dec, x :: seen)
          else
            return (ltx, seen)
      | _ => return (ltx, seen)
      )
  do
  let mut ltx : LocalContext := {}
  for ugi in coherentUGinds do
    let n := if st.uNodes.binSearchContains ugi (· < ·) then unode ugi else gnode ugi
    let dec ← (⟨n⟩ : FVarId).getDecl
    mtrace on .zero with s!"[prepareSandboxContext] adding {n} of type {← ppExpr dec.type}"
    ltx := ltx.addDecl dec
  let (fltx, _) ← help goal_type ltx []
  let ctx : Context :=  {lctx := fltx}
  let mvid ← mkFreshMVarId
  let mctx : MetavarContext := {}
  let mctx := mctx.addExprMVarDecl mvid `prepareSandboxContext fltx {} goal_type
  mtrace on .zero with s!"[prepareSandboxContext] made mvar with goal type {← ppExpr goal_type}"
  let state : State := {mctx := mctx}
  return ⟨ctx,state,mvid⟩


open Std


structure translateTermType where
  emvTran : Std.HashMap MVarId FVarId := {}
  lmvTran : Std.HashMap LMVarId Name := {}
  eC : Nat := 0
  lC : Nat := 0



partial def translateTerm (init : translateTermType)
  (back_id : Nat) (term : Expr) (mctx : MetavarContext)
  {α : Sort _} (k : Expr → translateTermType → MetaM α) : MetaM α :=
  term.onAllSubtermsWiWorkerCpsSkipTravState init (fun e _ ttt q => do
    match e with
    | .mvar mvid =>
        match ttt.emvTran[mvid]? with
        | .some fv => q (.ok (.fvar fv)) ttt
        | _ =>
          match mctx.eAssignment.find? mvid with
          | .some val => q (.ok val) ttt
          | _ =>
            match mctx.decls.find? mvid with
            | .none => throwError s!"[translateTerm] tactic term translation contains undeclared mvar {repr mvid}"
            | .some dec =>
              translateTerm ttt back_id dec.type mctx <| fun type ttt => do
                let tn := tnode back_id ttt.eC
                WithLocalDeclStd tn type do
                  q (.ok (.fvar ⟨tn⟩)) {ttt with eC := ttt.eC+1, emvTran := ttt.emvTran.insert mvid ⟨tn⟩}
    | .sort u =>
        let u := u.onAllSubterms (fun e =>
          match e with
          | .mvar mvid =>
            match mctx.lAssignment.find? mvid with
            | .some val => val
            | _ => e
          | _ => e
          )
        let ttt := u.onAllSubtermsFold ttt (fun e ttt =>
          match e with
          | .mvar mvid =>
              let tn := tnode back_id ttt.lC
              {ttt with lC := ttt.lC+1, lmvTran := ttt.lmvTran.insert mvid tn}
          | _ => ttt
          )
        let u := u.onAllSubterms (fun e =>
          match e with
          | .mvar mvid =>
            match ttt.lmvTran[mvid]? with
            | .some val => .param val
            | _ => e
          | _ => e
          )
        q (.ok (.sort u)) ttt
    | .const n us =>
        let mut ttt := ttt
        let mut rep := []
        for u in us do
          let u := u.onAllSubterms (fun e =>
            match e with
            | .mvar mvid =>
              match mctx.lAssignment.find? mvid with
              | .some val => val
              | _ => e
            | _ => e
            )
          ttt := u.onAllSubtermsFold ttt (fun e ttt =>
            match e with
            | .mvar mvid =>
                let tn := tnode back_id ttt.lC
                {ttt with lC := ttt.lC+1, lmvTran := ttt.lmvTran.insert mvid tn}
            | _ => ttt
            )
          let u := u.onAllSubterms (fun e =>
            match e with
            | .mvar mvid =>
              match ttt.lmvTran[mvid]? with
              | .some val => .param val
              | _ => e
            | _ => e
            )
          rep := u :: rep
        q (.ok (.const n rep.reverse)) ttt
    | _ => q (.ok e) ttt
    ) k

#check 1




def onGoalOnly'
  (target_goal_id : Nat)
  (cfg : SearchConfig) (st : SearchState (List Nat))
  (ctx : Context) (state : State) (mvid : MVarId)
  (action : MVarId → MetaM Bool) (actionName : String )
  {α : Sort _} (k : ListProd Nat Expr → ListProd Nat Expr → SearchState (List Nat) → MetaM α) : MetaM α :=
  trace set Tracing.Flags.none in do
  mtrace on .zero with s!"[onGoalOnly'] target_goal_id {target_goal_id}"
  try
    let (ok?,state) ← MetaM.run (action mvid) ctx state
    if !ok?
    then
      mtrace on .zero with s!"[onGoalOnly'] not ok"
      k .nil .nil st
    else
      match state.mctx.eAssignment.find? mvid with
      | .none =>
          mtrace on .zero with s!"[onGoalOnly'] unassignened goal mvar"
          k .nil .nil st
      | .some term =>
          mtrace on .zero with s!"[onGoalOnly'] raw term {term}" -- no pp as out of context
          translateTerm {} st.id_gen_back term state.mctx <| fun term ttt => do
            mtrace on .zero with s!"[onGoalOnly'] translated term {← ppExpr term}"
            let term ← unfoldAuxLemmas term
            if ← isTypeCorrect term
            then
              mtrace on .zero with s!"[onGoalOnly'] integrating"
              integrateBackwardStd
                cfg.revCountMax target_goal_id term (.string s!"[Tactic] {actionName}") ttt.eC .nil .nil st
                k
            else
              mtrace on .zero with s!"[onGoalOnly'] not type correct"
              let st := {st with id_gen_back := st.id_gen_back + 1} --necessary
              k .nil .nil st
  catch _ =>
    k .nil .nil st


def onGoalOnly
  (target_goal_id : Nat) (target_goal_type : Expr)
  (cfg : SearchConfig) (st : SearchState (List Nat))
  (action : MVarId → MetaM Bool) (actionName : String )
  {α : Sort _} (k : ListProd Nat Expr → ListProd Nat Expr → SearchState (List Nat) → MetaM α) : MetaM α :=
  trace set Tracing.Flags.none in do
  let ugis := st.introTree.gatherUGidsToGoalId target_goal_id []
  mtrace on .zero with s!"[onGoalOnly] ugis {ugis}"
  let ⟨ctx,state,mvid⟩ ← prepareSandboxContext st ugis target_goal_type
  onGoalOnly'
    target_goal_id cfg st ctx state mvid action actionName k


#check unfoldAuxLemmas


def onForwOnly
  (target_forw_id : Nat)
  (cfg : SearchConfig) (st : SearchState (List Nat))
  (action : MVarId → MetaM Bool) (actionName : String )
  {α : Sort _} (k : ListProd Nat Expr → ListProd Nat Expr → SearchState (List Nat) → MetaM α) : MetaM α :=
  trace set Tracing.Flags.none in do
  let (gid,ge) := st.introTree.topGoalForForwId target_forw_id
  mtrace on .zero with s!"[onForwOnly] gid {gid} ge {← ppExpr ge}"
  onGoalOnly gid ge cfg st action actionName k


def onGoalOnlyMulti
  (target_goal_id : Nat) (target_goal_type : Expr)
  (cfg : SearchConfig) (st : SearchState (List Nat))
  (actions : List (MVarId → MetaM Bool)) (actionName : String )
  {α : Sort _} (k : ListProd Nat Expr → ListProd Nat Expr → SearchState (List Nat) → MetaM α) : MetaM α :=
  trace set Tracing.Flags.none in do
  let ugis := st.introTree.gatherUGidsToGoalId target_goal_id []
  mtrace on .zero with s!"[onGoalOnlyMulti] ugis {ugis}"
  let ⟨ctx,state,mvid⟩ ← prepareSandboxContext st ugis target_goal_type
  actions.foldlMcps (⟨.nil, .nil, st⟩ : Prod3 (ListProd Nat Expr) (ListProd Nat Expr) (SearchState (List Nat))) (fun action A@⟨_,_,st⟩ k => do
    try
      let (ok?,state) ← MetaM.run (action mvid) ctx state
      if !ok?
      then
        k A
      else
        match state.mctx.eAssignment.find? mvid with
        | .none =>
            k A
        | .some term =>
            translateTerm {} st.id_gen_back term state.mctx <| fun term ttt => do
              let term ← unfoldAuxLemmas term
              if ← isTypeCorrect term
              then
                integrateBackwardStd
                  cfg.revCountMax target_goal_id term (.string s!"[Tactic] {actionName}") ttt.eC .nil .nil st
                  (fun nFs nGs st => k ⟨nFs,nGs,st⟩)
              else
                let st := {st with id_gen_back := st.id_gen_back + 1} --necessary
                k {A with thd := st}
    catch _ =>
      k A
    ) <| fun ⟨nFs,nGs,st⟩ => k nFs nGs st


#check 1


partial def Lean.Expr.getFvarIdsRec (e : Expr) (init : List FVarId) : MetaM (List FVarId) :=
  e.onAllSubtermsFoldNoPartialM init (fun e sofar =>
    match e with
    | .fvar fvid => do
        let T ← fvid.getType
        let next ← T.getFvarIdsRec sofar
        return next.insert fvid
    | _ => return sofar)


def onGoalStrictly'
  (target_goal_id : Nat)
  (cfg : SearchConfig) (st : SearchState (List Nat))
  (ctx : Context) (state : State) (mvid : MVarId)
  (action : MVarId → MetaM Bool) (actionName : String )
  {α : Sort _} (k : Bool → ListProd Nat Expr → ListProd Nat Expr → SearchState (List Nat) → MetaM α) : MetaM α :=
  trace set Tracing.Flags.none in do
  try
    let (ok?,state) ← MetaM.run (action mvid) ctx state
    if !ok?
    then
      mtrace on .zero with s!"[onGoalStrictly'] not ok"
      k false .nil .nil st
    else
      match state.mctx.eAssignment.find? mvid with
      | .none =>
          mtrace on .zero with s!"[onGoalStrictly'] unassigned goal mvar"
          k false .nil .nil st
      | .some term =>
          mtrace on .zero with s!"[onGoalStrictly'] raw term {term}"
          translateTerm {} st.id_gen_back term state.mctx <| fun term ttt => do
            mtrace on .zero with s!"[onGoalStrictly'] unassigned goal mvar"
            let term ← unfoldAuxLemmas term
            if ← isTypeCorrect term
            then
              mtrace on .zero with s!"[onGoalStrictly'] translated term {← ppExpr term}"
              integrateBackwardStd
                cfg.revCountMax target_goal_id term (.string s!"[Tactic] {actionName}") ttt.eC .nil .nil st
                (k true)
            else
              mtrace on .zero with s!"[onGoalStrictly'] not type correct"
              let st := {st with id_gen_back := st.id_gen_back + 1} --necessary
              k false .nil .nil st
  catch _ =>
    mtrace on .zero with s!"[onGoalStrictly'] failure, skip"
    k false .nil .nil st

def onGoalStrictly
  (target_goal_id : Nat) (target_goal_type : Expr)
  (cfg : SearchConfig) (st : SearchState (List Nat))
  (action : MVarId → MetaM Bool) (actionName : String )
  {α : Sort _} (k : ListProd Nat Expr → ListProd Nat Expr → SearchState (List Nat) → MetaM α) : MetaM α :=
  trace set Tracing.Flags.none in do
  let fvis ← target_goal_type.getFvarIdsRec []
  let mut ltx : LocalContext := {}
  for fvid in fvis do
    let dec ← fvid.getDecl
    ltx := ltx.addDecl dec
  let ctx : Context :=  {lctx := ltx}
  let mvid ← mkFreshMVarId
  let mctx : MetavarContext := {}
  let mctx := mctx.addExprMVarDecl mvid `onGoalStrictly ltx {} target_goal_type
  let state : State := {mctx := mctx}
  onGoalStrictly'
    target_goal_id cfg st ctx state mvid action actionName (fun _ => k)
