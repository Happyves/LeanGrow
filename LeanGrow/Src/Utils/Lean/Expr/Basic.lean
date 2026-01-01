

/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Utils.Lean.Expr.Subterms
import LeanGrow.Src.Utils.Lean.Expr.Collect
import LeanGrow.Src.Utils.Lean.MetaAPI
import LeanGrow.Src.Utils.Std.List
import LeanGrow.Src.Utils.Lean.Expr.Level
import LeanGrow.FFI.Lffi

open Lean Meta


-- # Binders

@[inline]
def Lean.Expr.getLamBody : Expr → Expr
| .lam _ _ b _ => b.getLamBody
| e => e

/-- Also handles let-/
@[specialize]
def Lean.Expr.surgeryForall (trafo : Expr → MetaM Expr) : Expr → MetaM Expr
  | .forallE n t b bi => return .forallE n t (← b.surgeryForall trafo) bi
  | .letE n t v b i => return .letE n t v (← b.surgeryForall trafo) i
  | x  => trafo x

/-- Also handles let-/
@[specialize]
def Lean.Expr.surgeryLambda (trafo : Expr → MetaM Expr) : Expr → MetaM Expr
  | .lam n t b bi => return .lam n t (← b.surgeryLambda trafo) bi
  | .letE n t v b i => return .letE n t v (← b.surgeryLambda trafo) i
  | x  => trafo x

/-- Also handles let-/
@[specialize]
def Lean.Expr.surgeryForallWD (trafo : Expr → Nat → MetaM Expr) (d : Nat) : Expr → MetaM Expr
  | .forallE n t b bi => return .forallE n t (← b.surgeryForallWD trafo (d+1)) bi
  | .letE n t v b i => return .letE n t v (← b.surgeryForallWD trafo (d+1)) i
  | x  => trafo x d

/-- Also handles let-/
@[specialize]
def Lean.Expr.surgeryBoundedForallWD (trafo : Expr → Nat → MetaM Expr) (d bound : Nat) (e : Expr) : MetaM Expr := do
  if bound == 0
  then trafo e d
  else
    match e with
    | .forallE n t b bi => return .forallE n t (← b.surgeryBoundedForallWD trafo (d+1) (bound - 1)) bi
    | .letE n t v b i => return .letE n t v (← b.surgeryBoundedForallWD trafo (d+1) (bound - 1)) i
    | x  => trafo x d



/-- Also handles let-/
@[specialize]
def Lean.Expr.surgeryLambdaWD (trafo : Expr → Nat →  MetaM Expr) (d : Nat) : Expr → MetaM Expr
  | .lam n t b bi => return .lam n t (← b.surgeryLambdaWD trafo (d+1)) bi
  | .letE n t v b i => return .letE n t v (← b.surgeryLambdaWD trafo (d+1)) i
  | x  => trafo x d

/-- Also handles let-/
@[specialize]
def Lean.Expr.lambdifyWD (trafo : Expr → Nat →  MetaM Expr) (d : Nat) : Expr → MetaM Expr
  | .forallE n t b bi => return .lam n t (← b.lambdifyWD trafo (d+1)) bi
  | .letE n t v b i => return .letE n t v (← b.lambdifyWD trafo (d+1)) i
  | x  => trafo x d


/-- Also handles let-/
@[specialize]
def Lean.Expr.surgeryBoundedLambdaWD (trafo : Expr → Nat →  MetaM Expr) (d bound : Nat) (e : Expr) : MetaM Expr :=
  if bound == 0
  then trafo e d
  else
    match e with
    | .lam n t b bi => return .lam n t (← b.surgeryBoundedLambdaWD trafo (d+1) (bound - 1)) bi
    | .letE n t v b i => return .letE n t v (← b.surgeryBoundedLambdaWD trafo (d+1) (bound - 1)) i
    | x  => trafo x d

/-- Also handles let-/
@[specialize]
def Lean.Expr.lambdifyBoundedWD (trafo : Expr → Nat →  MetaM Expr) (d bound : Nat) (e : Expr) : MetaM Expr :=
  if bound == 0
  then trafo e d
  else
    match e with
    | .forallE n t b bi => return .lam n t (← b.lambdifyBoundedWD trafo (d+1) (bound - 1)) bi
    | .letE n t v b i => return .letE n t v (← b.lambdifyBoundedWD trafo (d+1) (bound - 1)) i
    | x  => trafo x d


partial def Lean.Expr.zeta : Expr → Expr
  | .letE _ _ V B _ => (Expr.instantiate1 B V).zeta
  | x => x

@[inline]
def Lean.Expr.zetaFvs (within : Expr)
  (initD : LocalContext) (initI : LocalInstances) : MetaM Expr := do
  return (← within.onAllSubtermsM initD initI (fun
      | x@(.fvar fv), _, l1, l2 => do
          let dec ← fv.GetDecl l1 l2
          match dec with
          | .cdecl .. => return ⟨x,l1,l2⟩
          | .ldecl _ _ _ _ v .. => return ⟨v,l1,l2⟩
      | x,_,y,z => return ⟨x,y,z⟩)).1


-- # Abstract pattern

@[inline]
def Lean.Expr.abstractPat (pat within : Expr) : Expr :=
  within.onAllSubtermsWiDepth (fun x d =>
    if x == pat
    then
      .bvar d
    else
      match x with
      | .bvar i => if i ≥ d then .bvar (i+1) else x
      | _ => x)


@[inline]
def Lean.Expr.abstractPatBind (pat patType within : Expr) : Expr :=
  let absd := Expr.abstractPat pat within
  .lam `abstractPat.dummy patType absd .default



/--
- Expect fvars to be in context
- λ & let are in same order as `fvs`, without checking for consistency of abstraction !
-/
@[specialize]
partial def Lean.Expr.abstractLetFvarWrt
  (initD : LocalContext) (initI : LocalInstances)
  (fvs : Array FVarId) (e : Expr)
  : MetaM (Prod3 Expr LocalContext LocalInstances) :=
    let rec bind (term : Expr) (i : Nat) (initD : LocalContext) (initI : LocalInstances) : MetaM (Prod3 Expr LocalContext LocalInstances) := do
      match ← (fvs[i]!).GetDecl initD initI with
      | .cdecl _ _ _ T .. =>
          let ⟨T,initD,initI⟩ ← T.onAllSubtermsM initD initI (fun x d initD initI =>
            match x with
            | .fvar id =>
              match fvs.findIdx? (fun y => y == id) with
              | .none => return ⟨x,initD,initI⟩
              | .some j => return ⟨(.bvar (d + i - 1 - j)),initD,initI⟩
            | _ => return ⟨x,initD,initI⟩ )
          if i == 0
          then
            return ⟨.lam `abstractFvarWrt T term .default,initD,initI⟩
          else
            bind (.lam `abstractFvarWrt T term .default) (i-1) initD initI
      | .ldecl _ _ _ T V nonDep .. =>
          let ⟨T,initD,initI⟩ ← T.onAllSubtermsM initD initI (fun x d initD initI =>
            match x with
            | .fvar id =>
              match fvs.findIdx? (fun y => y == id) with
              | .none => return ⟨x,initD,initI⟩
              | .some j => return ⟨(.bvar (d + i - 1 - j)),initD,initI⟩
            | _ => return ⟨x,initD,initI⟩ )
          if i == 0
          then
            return ⟨.letE `abstractFvarWrt T V term nonDep,initD,initI⟩
          else
            bind (.letE `abstractFvarWrt T V term nonDep) (i-1) initD initI
    do
    let fvS := fvs.size
    if fvS == 0
    then return ⟨e,initD,initI⟩
    else
      let ⟨absd,initD,initI⟩ ← e.onAllSubtermsM initD initI (fun x d initD initI =>
        match x with
        | .fvar id =>
          match fvs.findIdx? (fun y => y == id) with
          | .none => return ⟨x,initD,initI⟩
          | .some i => return ⟨(.bvar (d + fvS - 1 - i)),initD,initI⟩
        | _ => return ⟨x,initD,initI⟩ )
      bind absd (fvs.size - 1) initD initI



/--
- Expect fvars to be in context
- ∀ & let are in same order as `fvs`,  without checking for consistency of abstraction !
-/
@[specialize]
partial def Lean.Expr.abstractLetFvarAsAllWrt
  (initD : LocalContext) (initI : LocalInstances)
  (fvs : Array FVarId) (e : Expr)
  : MetaM (Prod3 Expr LocalContext LocalInstances) :=
    let rec bind (term : Expr) (i : Nat) (initD : LocalContext) (initI : LocalInstances) : MetaM (Prod3 Expr LocalContext LocalInstances) := do
      match ← (fvs[i]!).GetDecl initD initI with
      | .cdecl _ _ _ T .. =>
          let ⟨T,initD,initI⟩ ← T.onAllSubtermsM initD initI (fun x d initD initI =>
            match x with
            | .fvar id =>
              match fvs.findIdx? (fun y => y == id) with
              | .none => return ⟨x,initD,initI⟩
              | .some j => return ⟨(.bvar (d + i - 1 - j)),initD,initI⟩
            | _ => return ⟨x,initD,initI⟩ )
          if i == 0
          then
            return ⟨.forallE `abstractFvarWrt T term .default,initD,initI⟩
          else
            bind (.forallE `abstractFvarWrt T term .default) (i-1) initD initI
      | .ldecl _ _ _ T V nonDep .. =>
          let ⟨T,initD,initI⟩ ← T.onAllSubtermsM initD initI (fun x d initD initI =>
            match x with
            | .fvar id =>
              match fvs.findIdx? (fun y => y == id) with
              | .none => return ⟨x,initD,initI⟩
              | .some j => return ⟨(.bvar (d + i - 1 - j)),initD,initI⟩
            | _ => return ⟨x,initD,initI⟩ )
          if i == 0
          then
            return ⟨.letE `abstractFvarWrt T V term nonDep,initD,initI⟩
          else
            bind (.letE `abstractFvarWrt T V term nonDep) (i-1) initD initI
    do
    let fvS := fvs.size
    if fvS == 0
    then return ⟨e,initD,initI⟩
    else
      let ⟨absd,initD,initI⟩ ← e.onAllSubtermsM initD initI (fun x d initD initI =>
        match x with
        | .fvar id =>
          match fvs.findIdx? (fun y => y == id) with
          | .none => return ⟨x,initD,initI⟩
          | .some i => return ⟨(.bvar (d + fvS - 1 - i)),initD,initI⟩
        | _ => return ⟨x,initD,initI⟩ )
      bind absd (fvs.size - 1) initD initI


@[inline]
partial def Lean.Expr.instantiateLooseBvarsL (fvs : List FVarId) (e : Expr) : Expr :=
    e.onAllSubtermsWiDepth (fun x d =>
        match x with
        | .bvar i =>
            if  i ≥ d
            then
              let fid := fvs[i - d]!
              (.fvar fid)
            else
              x
        | _ => x )

@[inline]
partial def Lean.Expr.instantiateLooseBvarsA (fvs : Array FVarId) (e : Expr) : Expr :=
    e.onAllSubtermsWiDepth (fun x d =>
        match x with
        | .bvar i =>
            if  i ≥ d
            then
              let fid := fvs[i - d]!
              (.fvar fid)
            else
              x
        | _ => x )



-- # Check pattern

@[inline]
def Lean.Expr.hasPattern (pat within : Expr) : Bool :=
  within.onAllSubtermsCheckExists (fun x => x == pat)

@[inline]
def Lean.Expr.hasWorker (within : Expr) : Bool :=
  within.onAllSubtermsCheckExists (fun | .fvar x => x.isWorker | _ => false)


@[inline]
def Lean.Expr.hasPatternTR (pat within : Expr) : Bool :=
  within.onAllSubtermsCheckExistsTR (fun x => x == pat)

@[inline]
def Lean.Expr.hasWorkerTR (within : Expr) : Bool :=
  within.onAllSubtermsCheckExistsTR (fun | .fvar x => x.isWorker | _ => false)

@[inline]
def Lean.Expr.hasWorkerExcpet (exe : List FVarId) (within : Expr) : Bool :=
  within.onAllSubtermsCheckExists (fun | .fvar x => if x.isWorker then !(exe.contains x) else false | _ => false)


@[inline]
def Lean.Expr.hasWorkerExcpetTR (exe : List FVarId) (within : Expr) : Bool :=
  within.onAllSubtermsCheckExistsTR (fun | .fvar x => if x.isWorker then !(exe.contains x) else false | _ => false)


@[inline]
def Lean.Expr.hasTnodes (within : Expr) : Bool :=
  within.onAllSubtermsCheckExists (fun
    | .fvar ⟨(.num (.num ..) ..)⟩ => true
    | .sort u => u.hasTnodes
    | .const _ lvls => lvls.any Level.hasTnodes
    | _ => false)

@[inline]
def Lean.Expr.hasTnodesTR (within : Expr) : Bool :=
  within.onAllSubtermsCheckExistsTR (fun
    | .fvar ⟨(.num (.num ..) ..)⟩ => true
    | .sort u => u.hasTnodes
    | .const _ lvls => lvls.any Level.hasTnodes
    | _ => false)

@[inline]
def Lean.Expr.hasLnodes (within : Expr) : Bool :=
  within.onAllSubtermsCheckExists (fun | .mvar ⟨(.num (.num ..) ..)⟩ => true | _ => false)


@[inline]
def Lean.Expr.hasLnodesTR (within : Expr) : Bool :=
  within.onAllSubtermsCheckExistsTR (fun | .mvar ⟨(.num (.num ..) ..)⟩ => true | _ => false)



-- # Collect

@[inline]
def Lean.Expr.getFVars (e : Expr) : List Expr :=
  e.onAllSubtermsFoldSkip []
    (fun x sofar =>
      match x with
      | .fvar .. => (sofar.insert x, true)
      | _ => (sofar, !x.hasFVar)
      )

@[inline]
def Lean.Expr.getFVarIds (e : Expr) : List FVarId :=
  e.onAllSubtermsFoldSkip []
    (fun x sofar =>
      match x with
      | .fvar id => (sofar.insert id, true)
      | _ => (sofar, !x.hasFVar)
      )

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
def Lean.Expr.getWorkerInds (proof : Expr) : Array Nat :=
  let res := proof.onAllSubtermsFoldSkip (UInt32Array.emptyWithCapacity 4) (fun e st =>
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
def Lean.Expr.getWorkerIndsTrans (l1 : LocalContext) (l2 : LocalInstances) (proof : Expr) : MetaM (Array Nat) := do
  let ⟨res,_,_⟩ ← proof.onAllSubtermsFoldEnqueueM l1 l2 (UInt32Array.emptyWithCapacity 4) (fun e D ws l1 l2 st =>
    match e with
    | .fvar fv@⟨(.num (.str _ k) d)⟩ => do
        if k == "w"
        then
          if ws.contains e
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
  return A


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


/-
Todo:

make skippable versions of `onAllSubtermsCheckExists` and `onAllSubtermsFoldEnqueueM`
and replace in above to check for fvars
.. actually, apply to `onAllSubtermsM` of this section too ...
-/
