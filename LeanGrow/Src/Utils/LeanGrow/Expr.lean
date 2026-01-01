
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Utils.Lean.Expr.Basic
import LeanGrow.Src.Utils.Lean.Expr.Level

open Lean Meta

@[inline]
def Lean.Expr.getWorkerFVarIds (e : Expr) : List FVarId :=
  e.onAllSubtermsFold []
    (fun x sofar =>
      match x with
      | (.fvar x@(⟨.num (.str _ k) _⟩)) =>
          if k == "w"
          then sofar.insert x -- no duplication
          else sofar
      | _ => sofar
      )


@[inline]
def Lean.Expr.getWorkers (e : Expr) : List Expr :=
  e.onAllSubtermsFold []
    (fun x sofar =>
      match x with
      | (.fvar (⟨.num (.str _ k) _⟩)) =>
          if k == "w"
          then sofar.insert x -- no duplication
          else sofar
      | _ => sofar
      )


@[inline]
partial def Lean.Expr.getWorkerFVarIdsTrans (e : Expr) (ini : List FVarId)
  (initD : LocalContext) (initI : LocalInstances)
  : MetaM (List FVarId) := do
  let ⟨res,_,_⟩ ← e.onAllSubtermsFoldEnqueueM initD initI ini
    (fun x _ localWorkas initD initI sofar =>
      match x with
      | (.fvar x@(⟨.num (.str _ k) _⟩)) => do
          if k == "w"
          then
            match localWorkas.find? x.name.toString.toUTF8 with
            | .some _ => return ⟨.std sofar,initD,initI⟩
            | .none =>
              let D :=
                match ← x.GetDecl initD initI with
                | .cdecl _ _ _ T .. => T
                | .ldecl _ _ _ _ V .. => V
              if D.data.hasFVar
              then return ⟨.enq (sofar.insert x) 0 D,initD,initI⟩
              else
                return ⟨.std (sofar.insert x),initD,initI⟩
          else return ⟨.std sofar,initD,initI⟩
      | _ => return ⟨.std sofar,initD,initI⟩
      )
  return res

structure TnodifyMVarsT where
  initTransTnodes : NameMap Name := {}
  initTransValues : NameMap Expr := {}
  initargIdx : Nat := 0
deriving Inhabited, Repr

/-- In expression `e`, replaces mvars with their assignements (if they have one),
or replcaes them by a tnode, which is add to context.
The follwoing inputs get modified and are expected by the continuation:
- `initTransTnodes` has as keys the mvarIds of `e`, and values the `tnode`-ids that subsitute them
- `initTransValues` has as keys the mvarIds of `e`, and values their assigned value (which has
  been recursivly cleaned of its mvars)
- `initargIdx` is the position index of tnodes we create ; we start at 0 ; in the continuation,
  it is the total number of tnodes created.
-/
@[specialize]
partial def instantiateOrTnodifyMVarsIn (backIdx : Nat) (e : Expr)
  (initD : LocalContext) (initI : LocalInstances)
  (st : TnodifyMVarsT) : MetaM (Prod4 Expr (TnodifyMVarsT) LocalContext LocalInstances) :=
  e.onAllSubtermsWiWorkerCpsSkipTravState initD initI st
    (fun e _ d@⟨tns,vals,_⟩ initD initI => do
      mtrace on .one with s!"looking at {← ppExpr e}"
      match e with
      | .mvar mvid@⟨mid⟩ =>
          match vals.find? mid with
          | .some V =>
              mtrace on .zero with s!"replaced by value {← ppExpr V}"
              return ⟨(.error V),d,initD,initI⟩
          | .none =>
            match tns.find? mid with
            | .some t =>
                mtrace on .zero with s!"replaced by tnode {t}"
                return ⟨(.error (.fvar ⟨t⟩)),d,initD,initI⟩
            | .none =>
                if ← mvid.isAssigned
                then
                  let val ← InstantiateMVars e initD initI
                  mtrace on .zero with s!"assigned mvar, procceding on value {← ppExpr val}"
                  let ⟨val,d,initD,initI⟩ ← instantiateOrTnodifyMVarsIn backIdx val initD initI d
                    mtrace on .zero with s!"returned from assigned mvar process with {← ppExpr val}"
                    let d := {d with initTransValues := d.initTransValues.insert mid val}
                    return ⟨(.error val),d,initD,initI⟩
                else
                  let T ← InferType e initD initI
                  mtrace on .zero with s!"unassigned mvar, procceding on type {← ppExpr T}"
                  let ⟨nT,d,initD,initI⟩ ← instantiateOrTnodifyMVarsIn backIdx T initD initI d
                    let node : Name := tnode backIdx d.3
                    mtrace on .zero with s!"returning from unassigned mvar, adding tnode {node} of type {← ppExpr nT}"
                    let d := {d with initTransTnodes := d.initTransTnodes.insert mid node, initargIdx := d.initargIdx + 1}
                    let ⟨fv,initD,initI⟩ ← WithLocalDecl node nT initD initI
                    return ⟨(.error (.fvar fv)),d ,initD,initI⟩
      | _ => return ⟨.ok e,d ,initD,initI⟩
      )


partial def instantiateOrTnodifyMVarsMulti (backIdx : Nat) (es : Array Expr)
  (initD : LocalContext) (initI : LocalInstances) (st : TnodifyMVarsT) --(initTransTnodes : NameMap Name := {}) (initTransValues : NameMap Expr := {}) (initargIdx : Nat := 0)
  : MetaM (Prod4 (Array Expr) (TnodifyMVarsT) LocalContext LocalInstances) :=
  let rec go (i : Nat) (res : Array Expr) (st : TnodifyMVarsT) (initD : LocalContext) (initI : LocalInstances) --(tt : NameMap Name) (tv : NameMap Expr) (idx : Nat) : MetaM α :=
    : MetaM (Prod4 (Array Expr) (TnodifyMVarsT) LocalContext LocalInstances) := do
    if i == res.size
    then return ⟨res,st,initD, initI⟩
    else
      let ⟨here,st,initD,initI⟩ ← instantiateOrTnodifyMVarsIn backIdx es[i]! initD initI st
      mtrace on .zero with s!"translated {es[i]!} to {← ppExpr here}"
      go (i+1) (res.set! i here) st initD initI
  go 0 es st initD initI


@[inline]
def mvarifyLTnodesIn (e : Level) (initD : LocalContext) (initI : LocalInstances) : MetaM (Prod3 Level LocalContext LocalInstances) :=
  e.onAllSubtermsMTR initD initI (fun
    | x@(.param mid),initD,initI => do
        match mid with
        | (.num (.num _ _) _) =>
          let mv ← mkLevelMVarOfName mid
          return ⟨mv,initD,initI⟩
        | _ => return ⟨x,initD,initI⟩
    | x,initD,initI => return ⟨x,initD,initI⟩
    )


@[inline]
partial def mvarifyTnodesRecWiContextIn (e : Expr) (initD : LocalContext) (initI : LocalInstances) : MetaM (Prod3 Expr LocalContext LocalInstances) :=
  e.onAllSubtermsMTR initD initI (fun
    | x@(.fvar mid),initD,initI =>
        match mid.name with
        | y@(.num (.num _ _) _) => do
            let T ← mid.GetType initD initI
            if T.hasTnodes
            then
              let ⟨T,initD,initI⟩ ← mvarifyTnodesRecWiContextIn T initD initI
              let mT ← mkMvarStdWiCoE y T initD initI
              return ⟨mT,initD,initI⟩
            else
              let mT ← mkMvarStdWiCoE y T initD initI
              return ⟨mT,initD,initI⟩
        | _ => return ⟨x,initD,initI⟩
    | .sort u,initD,initI => do
        let ⟨u,initD,initI⟩ ← mvarifyLTnodesIn u initD initI
        let x := .sort u
        return ⟨x,initD,initI⟩
    | .const n lvl,initD,initI => do
        let ⟨us,initD,initI⟩ : Prod3 (List Level) LocalContext LocalInstances :=
          ← lvl.foldlM (fun ⟨us,initD,initI⟩ u => do let ⟨u,initD,initI⟩ ← mvarifyLTnodesIn u initD initI ; return ⟨u :: us,initD,initI⟩) ⟨[],initD,initI⟩
        let x := .const n us.reverse
        return ⟨x,initD,initI⟩
    | x,initD,initI => return ⟨x,initD,initI⟩
    )


/-- Assumes expression has **no** tnodes-/
@[inline]
def getFirstLnodeDataFrom (e : Expr) : Option (Name × Nat) :=
  e.onAllSubtermsgetFirst (fun
    | .mvar ⟨.num (.num module thmIdx) _⟩ => .some (module, thmIdx)
    | .sort u => u.onAllSubtermsgetFirst (fun
        | .mvar ⟨.num (.num module thmIdx) _⟩ => .some (module, thmIdx)
        | _ => .none
        )
    | .const _ us => Id.run do
        for u in us do
          let here := u.onAllSubtermsgetFirst (fun
            | .mvar ⟨.num (.num module thmIdx) _⟩ => .some (module, thmIdx)
            | _ => .none
            )
          match here with
          | .some .. => return here
          | _ => continue
        return .none
    | _ => .none
    )


partial def Lean.Expr.abstractWorkers (e : Expr) (initD : LocalContext) (initI : LocalInstances)
  : MetaM (Expr × Array Expr) := do
    let ws := (← e.getWorkerFVarIdsTrans [] initD initI).mergeSort (fun x y =>
      match x.name, y.name with
      | .num _ i, .num _ j => i ≥ j -- sort deepest first
      | _, _ => panic s!"[Expr.abstractWorkers] unexpected worker formats {x.name} {y.name}")
    let e ← ws.foldlM (fun e fv => do
      match ← fv.GetDecl initD initI with
      | .cdecl _ _ _ T .. =>
           return (.lam `abstractFvarWrt T (Expr.abstractPat (Expr.fvar fv) e) .default)
      | .ldecl _ _ _ T V nonDep .. =>
          return (.letE `abstractFvarWrt T V (Expr.abstractPat (.fvar fv) e) nonDep)
      ) e
    let ws := (ws.foldl (fun A fvid => (Expr.fvar fvid) :: A) []).toArray
    return ⟨e,ws⟩



/-- Ouput is *not* sorted wrt deps-/
def augmentWorkersByDeps' (init : List FVarId) (extWorkas : List FVarId) : MetaM (List FVarId) :=
  let allws := extWorkas.reverse -- because we stacked them, so this is the order of dependecies ; we neeed this for transitive deps
  allws.foldlM (fun A fv => do
    if A.contains fv
    then return A
    else
      let T :=
        match ← fv.getDecl with
        | .cdecl _ _ _ T .. => T
        | .ldecl _ _ _ _ V .. => V
      if T.onAllSubtermsCheckExistsTR (fun
        | (.fvar c) => A.contains c
        | _ => false)
        then return fv :: A
        else return A
    ) init


/--  uses ∀ bindings-/
-- @[inline]
partial def Lean.Expr.abstractWorkersSpe' (e : Expr) (extWorkas : List FVarId) (initD : LocalContext) (initI : LocalInstances)
  : MetaM (Expr × Array Expr) := do
    let ws := (← augmentWorkersByDeps' (← e.getWorkerFVarIdsTrans [] initD initI) extWorkas).mergeSort (fun x y =>
      match x.name, y.name with
      | .num _ i, .num _ j => i ≥ j -- sort deepest first
      | _, _ => panic s!"[Expr.abstractWorkers] unexpected worker formats {x.name} {y.name}")
    let e ← ws.foldlM (fun e fv => do
      match ← fv.GetDecl initD initI with
      | .cdecl _ _ _ T .. =>
           return (.lam `abstractFvarWrt T (Expr.abstractPat (Expr.fvar fv) e) .default)
      | .ldecl _ _ _ T V nonDep .. =>
          return (.letE `abstractFvarWrt T V (Expr.abstractPat (.fvar fv) e) nonDep)
      ) e
    let ws := (ws.foldl (fun A fvid => (Expr.fvar fvid) :: A) []).toArray
    return ⟨e,ws⟩





@[inline]
def Lean.Expr.getLnodes (e : Expr) : List Expr :=
  e.onAllSubtermsFold []
    (fun x sofar =>
      match x with
      | (.mvar (⟨.num (.num _ _) _⟩)) =>
          sofar.insert x -- no duplication
      | _ => sofar
      )

@[inline]
def Lean.Expr.getLnodePos (e : Expr) : List Nat :=
  e.onAllSubtermsFold []
    (fun x sofar =>
      match x with
      | (.mvar (⟨.num (.num _ _) pos⟩)) =>
          sofar.insert pos -- no duplication
      | _ => sofar
      )
