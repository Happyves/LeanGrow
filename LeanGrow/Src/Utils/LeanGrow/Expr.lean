
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Utils.Lean.Expr.Basic
import LeanGrow.Src.Utils.Lean.Expr.Level

open Lean Meta


@[inline]
def Lean.Expr.getDeepestWorker (proof : Expr) : Option Nat :=
  proof.onAllSubtermsFoldSkip .none (fun e st =>
    match e with
    | .fvar ⟨.num (.str _ k) d⟩ =>
        if k == "w"
        then
          match st with
          | .none => (.some d, true)
          | .some x =>
              if d > x
              then (.some d,true)
              else (st,true)
        else (st,true)
    | _ => (st, !e.hasFVar)
    )


@[inline]
private def Lean.Expr.getWorkerIndsI (init : UInt32Array) (proof : Expr) : Array Nat :=
  let res := proof.onAllSubtermsFoldSkip init (fun e st =>
    match e with
    | .fvar ⟨.num (.str _ k) d⟩ =>
        if k == "w"
        then (st.oInsert d.toUInt32,true)
        else (st,true)
    | _ => (st,!e.hasFVar)
    )
  Id.run <| do
    let mut A := Array.emptyWithCapacity res.size
    for i in res do
      A := A.push i.toNat
    return A

@[inline]
def Lean.Expr.getWorkerInds (proof : Expr) : Array Nat :=
  proof.getWorkerIndsI (UInt32Array.emptyWithCapacity 4)


@[inline]
def Lean.Expr.getWorkerIndsTransTR (l1 : LocalContext) (l2 : LocalInstances) (proof : Expr) : MetaM (Prod3 (Array Nat) LocalContext LocalInstances) := do
  let ⟨res,r1,r2⟩ ← proof.onAllSubtermsFoldEnqueueM l1 l2 (UInt32Array.emptyWithCapacity 4) (fun e D ws l1 l2 st =>
    match e with
    | .fvar fv@⟨(.num (.str _ k) d)⟩ => do
        if k == "w"
        then
          if !(ws.contains e)
          then
            let st := st.oInsert d.toUInt32
            let T ← fv.GetType l1 l2
            if T.hasFVar
            then
              return ⟨.enq st D T,l1,l2⟩
            else
              return ⟨.std st,l1,l2⟩
          else
            return ⟨.std st,l1,l2⟩
        else return ⟨.std st,l1,l2⟩
    | _ => return ⟨.std st,l1,l2⟩
    )
  let mut A := Array.emptyWithCapacity res.size
  for i in res do
    A := A.push i.toNat
  return ⟨A,r1,r2⟩


@[inline]
private partial def Lean.Expr.getWorkerIndsTransR (ini : UInt32Array) (l1 : LocalContext) (l2 : LocalInstances) (proof : Expr) : MetaM (Prod3 UInt32Array LocalContext LocalInstances) := do
  proof.onAllSubtermsFoldSkipM l1 l2 ini (fun e _ ws l1 l2 st =>
    match e with
    | .fvar fv@⟨.num (.str _ k) d⟩ => do
        if k == "w"
        then
          if !(ws.contains e)
          then
            let st := st.oInsert d.toUInt32
            let T ← fv.GetType l1 l2
            if T.hasFVar
            then
              let ⟨st,l1,l2⟩ ← T.getWorkerIndsTransR st l1 l2
              return ⟨st,true,l1,l2⟩
            else
              return ⟨st,true,l1,l2⟩
          else
            return ⟨st,true,l1,l2⟩
        else
          return ⟨st,true,l1,l2⟩
    | _ => return ⟨st,!e.hasFVar,l1,l2⟩
    )



@[inline]
def Lean.Expr.getWorkerIndsTrans (l1 : LocalContext) (l2 : LocalInstances) (proof : Expr) : MetaM (Prod3 (Array Nat) LocalContext LocalInstances) := do
  let ⟨res,r1,r2⟩ ← proof.getWorkerIndsTransR (UInt32Array.emptyWithCapacity 4) l1 l2
  let mut A := Array.emptyWithCapacity res.size
  for i in res do
    A := A.push i.toNat
  return ⟨A,r1,r2⟩


@[inline]
def Lean.Expr.getGUFVarsIds (e : Expr) : List FVarId :=
  e.onAllSubtermsFoldSkip []
    (fun x sofar =>
      match x with
      | .fvar y@⟨.num k _⟩ =>
        if k == `u || k == `g
        then (sofar.insert y,true)
        else (sofar,true)
      | _ => (sofar, !x.hasFVar)
      )

@[inline]
def Lean.Expr.getGUFVarsIds' (ini : List FVarId) (e : Expr) : List FVarId :=
  e.onAllSubtermsFoldSkip ini
    (fun x sofar =>
      match x with
      | .fvar y@⟨.num k _⟩ =>
        if k == `u || k == `g
        then (sofar.insert y,true)
        else (sofar,true)
      | _ => (sofar, !x.hasFVar)
      )

@[inline]
def Lean.Expr.getWorkerFVarIds (e : Expr) : List FVarId :=
  e.onAllSubtermsFoldSkip []
    (fun x sofar =>
      match x with
      | (.fvar x@(⟨.num (.str _ k) _⟩)) =>
          if k == "w"
          then (sofar.insert x,true) -- no duplication
          else (sofar,true)
      | x => (sofar, !x.hasFVar)
      )


@[inline]
def Lean.Expr.getWorkers (e : Expr) : List Expr :=
  e.onAllSubtermsFoldSkip []
    (fun x sofar =>
      match x with
      | (.fvar (⟨.num (.str _ k) _⟩)) =>
          if k == "w"
          then (sofar.insert x,true) -- no duplication
          else (sofar,true)
      | x => (sofar, !x.hasFVar)
      )


@[inline]
partial def Lean.Expr.getWorkerFVarIdsTransTR (e : Expr) (ini : List FVarId)
  (initD : LocalContext) (initI : LocalInstances)
  : MetaM (List FVarId) := do
  let ⟨res,_,_⟩ ← e.onAllSubtermsFoldEnqueueM initD initI ini
    (fun X _ localWorkas initD initI sofar =>
      match X with
      | (.fvar x@(⟨.num (.str _ k) _⟩)) => do
          if k == "w"
          then
            if localWorkas.contains X
            then return ⟨.std sofar,initD,initI⟩
            else
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


@[inline]
partial def Lean.Expr.getWorkerFVarIdsTransR (ini : (Array FVarId)) (l1 : LocalContext) (l2 : LocalInstances) (proof : Expr) : MetaM (Prod3 (Array FVarId) LocalContext LocalInstances) := do
  proof.onAllSubtermsFoldSkipM l1 l2 ini (fun e _ ws l1 l2 st =>
    match e with
    | .fvar fv@⟨.num (.str _ k) _⟩ => do
        if k == "w"
        then
          if !(ws.contains e)
          then
            let st := (if st.contains fv then st else st.push fv)
            let T ← fv.GetType l1 l2
            if T.hasFVar
            then
              let ⟨st,l1,l2⟩ ← T.getWorkerFVarIdsTransR st l1 l2
              return ⟨st,true,l1,l2⟩
            else
              return ⟨st,true,l1,l2⟩
          else
            return ⟨st,true,l1,l2⟩
        else
          return ⟨st,true,l1,l2⟩
    | _ => return ⟨st,!e.hasFVar,l1,l2⟩
    )

@[inline]
def Lean.Expr.getWorkerFVarIdsTrans (l1 : LocalContext) (l2 : LocalInstances) (proof : Expr) : MetaM (Prod3 (Array FVarId) LocalContext LocalInstances) := do
  proof.getWorkerFVarIdsTransR (.emptyWithCapacity 4) l1 l2



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
      mtracing
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
                  if T.hasMVar
                  then
                    mtrace on .zero with s!"unassigned mvar, procceding on type {← ppExpr T}"
                    let ⟨nT,d,initD,initI⟩ ← instantiateOrTnodifyMVarsIn backIdx T initD initI d
                    let node : Name := tnode backIdx d.3
                    mtrace on .zero with s!"returning from unassigned mvar, adding tnode {node} of type {← ppExpr nT}"
                    let d := {d with initTransTnodes := d.initTransTnodes.insert mid node, initargIdx := d.initargIdx + 1}
                    let ⟨fv,initD,initI⟩ ← WithLocalDecl node nT initD initI
                    return ⟨(.error (.fvar fv)),d ,initD,initI⟩
                  else
                    let node : Name := tnode backIdx d.3
                    mtrace on .zero with s!"Adding tnode {node} of type {← ppExpr T}"
                    let d := {d with initTransTnodes := d.initTransTnodes.insert mid node, initargIdx := d.initargIdx + 1}
                    let ⟨fv,initD,initI⟩ ← WithLocalDecl node T initD initI
                    return ⟨(.error (.fvar fv)),d ,initD,initI⟩
      | _ => return ⟨.ok e,d ,initD,initI⟩
      )



@[inline]
partial def instantiateOrTnodifyMVarsMulti (backIdx : Nat) (es : Array Expr)
  (initD : LocalContext) (initI : LocalInstances) (st : TnodifyMVarsT) --(initTransTnodes : NameMap Name := {}) (initTransValues : NameMap Expr := {}) (initargIdx : Nat := 0)
  : MetaM (Prod4 (Array Expr) (TnodifyMVarsT) LocalContext LocalInstances) :=
  let rec go (i : Nat) (res : Array Expr) (st : TnodifyMVarsT) (initD : LocalContext) (initI : LocalInstances) --(tt : NameMap Name) (tv : NameMap Expr) (idx : Nat) : MetaM α :=
    : MetaM (Prod4 (Array Expr) (TnodifyMVarsT) LocalContext LocalInstances) := do
    mtracing
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
partial def mvarifyTnodesRec (e : Expr) (initD : LocalContext) (initI : LocalInstances) : MetaM (Prod3 Expr LocalContext LocalInstances) :=
  e.onAllSubtermsMTR initD initI (fun
    | x@(.fvar mid),_,initD,initI =>
        match mid.name with
        | y@(.num (.num _ _) _) => do
            let T ← mid.GetType initD initI
            if T.hasTnodes
            then
              let ⟨T,initD,initI⟩ ← mvarifyTnodesRec T initD initI
              let mT ← mkMvarStdNoCoE y T
              return ⟨mT,initD,initI⟩
            else
              let mT ← mkMvarStdNoCoE y T
              return ⟨mT,initD,initI⟩
        | _ => return ⟨x,initD,initI⟩
    | .sort u,_,initD,initI => do
        let ⟨u,initD,initI⟩ ← mvarifyLTnodesIn u initD initI
        let x := .sort u
        return ⟨x,initD,initI⟩
    | .const n lvl,_,initD,initI => do
        let ⟨us,initD,initI⟩ : Prod3 (List Level) LocalContext LocalInstances :=
          ← lvl.foldlM (fun ⟨us,initD,initI⟩ u => do let ⟨u,initD,initI⟩ ← mvarifyLTnodesIn u initD initI ; return ⟨u :: us,initD,initI⟩) ⟨[],initD,initI⟩
        let x := .const n us.reverse
        return ⟨x,initD,initI⟩
    | x,_,initD,initI => return ⟨x,initD,initI⟩
    )


/-- Assumes expression has **no** tnodes in mvar format (fvar format ok)-/
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


/--
- Ouput is *not* sorted wrt deps
- reverses extWorkas
-/
@[inline]
def augmentWorkersByDeps' (init : List FVarId) (extWorkas : List FVarId) : MetaM (List FVarId) :=
  let allws := extWorkas.reverse -- because we stacked them, so this is the order of dependecies ; we neeed this for transitive deps
  allws.foldlM (fun A fv => do
    if A.contains fv
    then return A
    else
      match ← fv.getDecl with
      | .cdecl _ _ _ T .. =>
        if T.onAllSubtermsCheckExistsTR (fun
          | (.fvar c) => A.contains c
          | _ => false)
        then return fv :: A
        else return A
      | .ldecl _ _ _ T V .. =>
        if T.onAllSubtermsCheckExistsTR (fun
          | (.fvar c) => A.contains c
          | _ => false)
        then return fv :: A
        else
          if V.onAllSubtermsCheckExistsTR (fun
            | (.fvar c) => A.contains c
            | _ => false)
          then return fv :: A
          else return A

    ) init

/--
- Ouput is *not* sorted wrt deps
- reverses extWorkas
-/
@[inline]
def augmentWorkersByDepsA (init : Array FVarId) (extWorkas : List FVarId) : MetaM (Array FVarId) :=
  let allws := extWorkas.reverse -- because we stacked them, so this is the order of dependecies ; we neeed this for transitive deps
  allws.foldlM (fun A fv => do
    if A.contains fv
    then return A
    else
      match ← fv.getDecl with
      | .cdecl _ _ _ T .. =>
        if T.onAllSubtermsCheckExistsTR (fun
          | (.fvar c) => A.contains c
          | _ => false)
        then return A.push fv
        else return A
      | .ldecl _ _ _ T V .. =>
        if T.onAllSubtermsCheckExistsTR (fun
          | (.fvar c) => A.contains c
          | _ => false)
        then return A.push fv
        else
          if V.onAllSubtermsCheckExistsTR (fun
            | (.fvar c) => A.contains c
            | _ => false)
          then return A.push fv
          else return A

    ) init

/-- Array has deepest vars last -/
@[inline]
def Lean.Expr.abstractWorkers (e : Expr) (initD : LocalContext) (initI : LocalInstances)
  : MetaM (Prod4 Expr (Array FVarId) LocalContext LocalInstances) := do
    let ws := (← e.getWorkerFVarIdsTrans initD initI).1.qsort (fun x y =>
      match x.name, y.name with
      | .num _ i, .num _ j => i < j -- sort deepest last ; qsort expects strict order
      | _, _ => panic s!"[Expr.abstractWorkers] unexpected worker formats {x.name} {y.name}")
    let ⟨e,l1,l2⟩  ← abstractLetFvarLam initD initI ws e
    return ⟨e,ws,l1,l2⟩

/-- Array has deepest vars last -/
@[inline]
def Lean.Expr.abstractWorkersAll (e : Expr) (initD : LocalContext) (initI : LocalInstances)
  : MetaM (Prod4 Expr (Array FVarId) LocalContext LocalInstances) := do
    let ws := (← e.getWorkerFVarIdsTrans initD initI).1.qsort (fun x y =>
      match x.name, y.name with
      | .num _ i, .num _ j => i < j -- sort deepest last ; qsort expects strict order
      | _, _ => panic s!"[Expr.abstractWorkers] unexpected worker formats {x.name} {y.name}")
    let ⟨e,l1,l2⟩  ← abstractLetFvarAll initD initI ws e
    return ⟨e,ws,l1,l2⟩

/-- Array has deepest vars last -/
@[inline]
def Lean.Expr.abstractInnerWorkers (e : Expr) (extWorkers : Array FVarId) (initD : LocalContext) (initI : LocalInstances)
  : MetaM (Prod4 Expr (Array FVarId) LocalContext LocalInstances) := do
    let ws := ((← e.getWorkerFVarIdsTrans initD initI).1.filter (fun fv => !(extWorkers.contains fv))).qsort (fun x y =>
      match x.name, y.name with
      | .num _ i, .num _ j => i < j -- sort deepest last ; qsort expects strict order
      | _, _ => panic s!"[Expr.abstractWorkers] unexpected worker formats {x.name} {y.name}")
    let ⟨e,l1,l2⟩  ← abstractLetFvarLam initD initI ws e
    return ⟨e,ws,l1,l2⟩

/-- Array has deepest vars last -/
@[inline]
def Lean.Expr.abstractInnerWorkersAll (e : Expr) (extWorkers : Array FVarId) (initD : LocalContext) (initI : LocalInstances)
  : MetaM (Prod4 Expr (Array FVarId) LocalContext LocalInstances) := do
    let ws := ((← e.getWorkerFVarIdsTrans initD initI).1.filter (fun fv => !(extWorkers.contains fv))).qsort (fun x y =>
      match x.name, y.name with
      | .num _ i, .num _ j => i < j -- sort deepest last ; qsort expects strict order
      | _, _ => panic s!"[Expr.abstractWorkers] unexpected worker formats {x.name} {y.name}")
    let ⟨e,l1,l2⟩  ← abstractLetFvarAll initD initI ws e
    return ⟨e,ws,l1,l2⟩

/-- Array has deepest vars last -/
@[inline]
def Lean.Expr.abstractInnerWorkersAll' (e : Expr) (extWorkers : List FVarId) (initD : LocalContext) (initI : LocalInstances)
  : MetaM (Prod4 Expr (Array FVarId) LocalContext LocalInstances) := do
    let ws := ((← e.getWorkerFVarIdsTrans initD initI).1.filter (fun fv => !(extWorkers.contains fv))).qsort (fun x y =>
      match x.name, y.name with
      | .num _ i, .num _ j => i < j -- sort deepest last ; qsort expects strict order
      | _, _ => panic s!"[Expr.abstractWorkers] unexpected worker formats {x.name} {y.name}")
    let ⟨e,l1,l2⟩  ← abstractLetFvarAll initD initI ws e
    return ⟨e,ws,l1,l2⟩

/--
- uses ∀ bindings
- Array has deepest vars first

**DOUBLE CHECK USE...** and compare to ↑
-/
@[inline]
partial def Lean.Expr.abstractWorkersSpe (e : Expr) (extWorkas : List FVarId) (initD : LocalContext) (initI : LocalInstances)
  : MetaM (Expr × Array Expr) := do
    let ws := (← augmentWorkersByDepsA (← e.getWorkerFVarIdsTrans initD initI).1 extWorkas).qsort (fun x y =>
      match x.name, y.name with
      | .num _ i, .num _ j => i > j -- sort deepest first ; qsort expects strict order
      | _, _ => panic s!"[Expr.abstractWorkers] unexpected worker formats {x.name} {y.name}")
    let e ← ws.foldlM (fun e fv => do
      match ← fv.GetDecl initD initI with
      | .cdecl _ _ _ T .. =>
          match ← IsClass? T initD initI with
          | .none => return (.lam `abstractFvarWrt T (Expr.abstractPat (Expr.fvar fv) e) .default)
          | _ => return (.lam `abstractFvarWrt T (Expr.abstractPat (Expr.fvar fv) e) .instImplicit)
      | .ldecl _ _ _ T V nonDep .. =>
          return (.letE `abstractFvarWrt T V (Expr.abstractPat (.fvar fv) e) nonDep)
      ) e
    let ws := ws.reverse.map Expr.fvar
    return ⟨e,ws⟩



@[inline]
def Lean.Expr.getLnodes (e : Expr) : List Expr :=
  e.onAllSubtermsFoldSkip []
    (fun x sofar =>
      match x with
      | (.mvar (⟨.num (.num _ _) _⟩)) =>
          (sofar.insert x, true) -- no duplication
      | _ => (sofar, !x.hasMVar)
      )

@[inline]
def Lean.Expr.getLnodePos (e : Expr) : List Nat :=
  e.onAllSubtermsFoldSkip []
    (fun x sofar =>
      match x with
      | (.mvar (⟨.num (.num _ _) pos⟩)) =>
          (sofar.insert pos, true) -- no duplication
      | _ => (sofar, !x.hasMVar)
      )

/-- doesn' t retrieve level-tnodes-/
@[inline]
def Lean.Expr.getTnodes (e : Expr) : List Expr :=
  e.onAllSubtermsFoldSkip []
    (fun x sofar =>
      match x with
      | (.fvar (⟨.num (.num _ _) _⟩)) =>
          (sofar.insert x, true) -- no duplication
      | _ => (sofar, !x.hasFVar)
      )
