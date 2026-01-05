

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
def Lean.Expr.abstractPatBind (pat patType within : Expr) (binder : BinderInfo) : Expr :=
  let absd := Expr.abstractPat pat within
  .lam `abstractPat.dummy patType absd binder



/--
- Expect fvars to be in context
- λ & let are in same order as `fvs`, without checking for consistency of abstraction !
-/
@[inline]
partial def Lean.Expr.abstractLetFvarLam
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
            match ← IsClass? T initD initI with
            | .none => return ⟨.lam `abstractFvarWrt T term .default,initD,initI⟩
            | _ => return ⟨.lam `abstractFvarWrt T term .instImplicit,initD,initI⟩
          else
            match ← IsClass? T initD initI with
            | .none => bind (.lam `abstractFvarWrt T term .default) (i-1) initD initI
            | _ => bind (.lam `abstractFvarWrt T term .instImplicit) (i-1) initD initI
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
@[inline]
partial def Lean.Expr.abstractLetFvarAll
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
            match ← IsClass? T initD initI with
            | .none => return ⟨.forallE `abstractFvarWrt T term .default,initD,initI⟩
            | _ => return ⟨.forallE `abstractFvarWrt T term .instImplicit,initD,initI⟩
          else
            match ← IsClass? T initD initI with
            | .none => bind (.forallE `abstractFvarWrt T term .default) (i-1) initD initI
            | _ => bind (.forallE `abstractFvarWrt T term .instImplicit) (i-1) initD initI
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



@[inline, specialize]
partial def Lean.Expr.instantiateLooseBvar (fvs : List FVarId) (e : Expr) : Expr :=
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
  within.onAllSubtermsCheckExistsSkip (fun | .fvar x => (x.isWorker,true) | x => (false, !x.hasFVar))


@[inline]
def Lean.Expr.hasPatternTR (pat within : Expr) : Bool :=
  within.onAllSubtermsCheckExistsTR (fun x => x == pat)

@[inline]
def Lean.Expr.hasWorkerTR (within : Expr) : Bool :=
  within.onAllSubtermsCheckExistsSkipTR (fun | .fvar x => (x.isWorker,true) | x => (false, !x.hasFVar))

@[inline]
def Lean.Expr.hasWorkerExcpet (exe : List FVarId) (within : Expr) : Bool :=
  within.onAllSubtermsCheckExistsSkip (fun | .fvar x => if x.isWorker then (!(exe.contains x), true) else (false,true) | x => (false, !x.hasFVar))


@[inline]
def Lean.Expr.hasWorkerExcpetTR (exe : List FVarId) (within : Expr) : Bool :=
  within.onAllSubtermsCheckExistsSkipTR (fun | .fvar x => if x.isWorker then (!(exe.contains x), true) else (false,true) | x => (false, !x.hasFVar))


@[inline]
def Lean.Expr.hasTnodes (within : Expr) : Bool :=
  let sk (x : Expr) := !x.hasFVar && !x.hasLevelParam
  within.onAllSubtermsCheckExistsSkip (fun
    | .fvar ⟨(.num (.num ..) ..)⟩ => (true,true)
    | .sort u => (u.hasTnodes,true)
    | .const _ lvls => (lvls.any Level.hasTnodes,true)
    | x => (false, sk x))


@[inline]
def Lean.Expr.hasTnodesTR (within : Expr) : Bool :=
  let sk (x : Expr) := !x.hasFVar && !x.hasLevelParam
  within.onAllSubtermsCheckExistsSkipTR (fun
    | .fvar ⟨(.num (.num ..) ..)⟩ => (true,true)
    | .sort u => (u.hasTnodes,true)
    | .const _ lvls => (lvls.any Level.hasTnodes,true)
    | x => (false, sk x))

@[inline]
def Lean.Expr.hasLnodes (within : Expr) : Bool :=
  within.onAllSubtermsCheckExistsSkip (fun | .mvar ⟨(.num (.num ..) ..)⟩ => (true,true) | x => (false, !x.hasMVar && !x.hasLevelMVar))


@[inline]
def Lean.Expr.hasLnodesTR (within : Expr) : Bool :=
  within.onAllSubtermsCheckExistsSkipTR (fun | .mvar ⟨(.num (.num ..) ..)⟩ => (true,true) | x => (false, !x.hasMVar && !x.hasLevelMVar))



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
def Lean.Expr.getFVarIds' (e : Expr) (ini : List FVarId) : List FVarId :=
  e.onAllSubtermsFoldSkip ini
    (fun x sofar =>
      match x with
      | .fvar id => (sofar.insert id, true)
      | _ => (sofar, !x.hasFVar)
      )
