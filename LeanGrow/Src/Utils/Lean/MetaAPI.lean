

import LeanGrowBeta.Utils.Lean.LocalContext
import LeanGrowBeta.Utils.Lean.MetavarContext

open Lean Meta



@[inline]
def clearMvarAssignments : MetaM Unit :=
  modifyMCtx (fun mc => {mc with lAssignment := {}, eAssignment := {}, dAssignment := {}})



-- # DefEq

/--
DefEq without failure (guarded).
Doesn't set the local context of mvars contain in `a` and `b` to the current one.
Clears, assignements from MetavarContext, and returns them.
-/
@[inline]
def defEqNoMv (a b : Expr) : MetaM (Option (PersistentHashMap LMVarId Level × PersistentHashMap MVarId Expr)) := do
  try
    if ← isExprDefEq a b
    then
      let mc ← getMCtx
      let rl := mc.lAssignment
      let re := mc.eAssignment
      clearMvarAssignments
      return .some (rl,re)
    else
      return .none
  catch _ => return .none

@[inline]
def defEqNoMvNoClear (a b : Expr) : MetaM (Option (PersistentHashMap LMVarId Level × PersistentHashMap MVarId Expr)) := do
  try
    if ← isExprDefEq a b
    then
      let mc ← getMCtx
      let rl := mc.lAssignment
      let re := mc.eAssignment
      return .some (rl,re)
    else
      return .none
  catch _ => return .none


@[inline]
partial def Lean.Expr.getMVarsRec (init : List MVarId) (e : Expr) : MetaM (List MVarId) :=
  let rec go (col : List MVarId) : List Expr → MetaM (List MVarId)
    | [] => return col
    | e :: more =>
        match e with
        | .mvar mid => do
            let T ← mid.getType
            if T.data.hasExprMVar
            then go (col.insert mid) (T :: more)
            else go (col.insert mid) more
        | .app l r => go (col) (l :: r :: more)
        | .lam _ l r _ => go (col) (l :: r :: more)
        | .forallE _ l r _ => go ( col)  (l :: r :: more)
        | .letE _ l r z _ => go ( col)  (l :: r :: z :: more)
        | .proj _ _ e => go ( col)  (e :: more)
        | .mdata _ e => go ( col) (e :: more)
        | _ => go ( col) more
  if e.data.hasExprMVar
  then go init [e]
  else return init


/--
DefEq without failure (guarded).
Sets the local context of mvars contain in `a` and `b` to the current one.
Clears, assignements from MetavarContext, and returns them.
Doesn't reset the local context of mvars contain in `a` and `b`.
-/
@[inline]
def defEqWiMv (a b : Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (Option (PersistentHashMap LMVarId Level × PersistentHashMap MVarId Expr)) := do
  withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
    let mva ← a.getMVarsRec []
    let mvb ← b.getMVarsRec mva
    for mv in mva do
      mv.setLocalData l1 l2
    for mv in mvb do
      mv.setLocalData l1 l2
    try
      if ← isExprDefEq a b
      then
        let mc ← getMCtx
        let rl := mc.lAssignment
        let re := mc.eAssignment
        clearMvarAssignments
        return .some (rl,re)
      else
        return .none
    catch _ => return .none

@[inline]
def defEqWiMvNoClear (a b : Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (Option (PersistentHashMap LMVarId Level × PersistentHashMap MVarId Expr)) := do
  withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
    let mva ← getMVars a
    let mvb ← getMVars b
    for mv in mva do
      mv.setLocalData l1 l2
    for mv in mvb do
      mv.setLocalData l1 l2
    try
      if ← isExprDefEq a b
      then
        let mc ← getMCtx
        let rl := mc.lAssignment
        let re := mc.eAssignment
        return .some (rl,re)
      else
        return .none
    catch _ => return .none



-- # Std

@[inline]
def Lean.FVarId.GetDecl (term : FVarId) (initD : LocalContext) (initI : LocalInstances) : MetaM LocalDecl := do
  withReader (fun ctx => {ctx with lctx := initD, localInstances := initI}) do
    term.getDecl

@[inline]
def Lean.FVarId.GetType (term : FVarId) (initD : LocalContext) (initI : LocalInstances) : MetaM Expr := do
  withReader (fun ctx => {ctx with lctx := initD, localInstances := initI}) do
    term.getType


@[inline]
def InferType (term : Expr) (initD : LocalContext) (initI : LocalInstances) : MetaM Expr := do
  withReader (fun ctx => {ctx with lctx := initD, localInstances := initI}) do
    inferType term

@[inline]
def InstantiateMVars (term : Expr) (initD : LocalContext) (initI : LocalInstances) : MetaM Expr := do
  withReader (fun ctx => {ctx with lctx := initD, localInstances := initI}) do
    instantiateMVars term

@[inline]
def Whnf (term : Expr) (initD : LocalContext) (initI : LocalInstances) : MetaM Expr := do
  withReader (fun ctx => {ctx with lctx := initD, localInstances := initI}) do
    whnf term

@[inline]
def WhnfAtMostI (term : Expr) (initD : LocalContext) (initI : LocalInstances) : MetaM Expr := do
  withReader (fun ctx => {ctx with lctx := initD, localInstances := initI}) do
    whnfAtMostI term

@[inline]
def WhnfD (term : Expr) (initD : LocalContext) (initI : LocalInstances) : MetaM Expr := do
  withReader (fun ctx => {ctx with lctx := initD, localInstances := initI}) do
    whnfD term

@[inline]
def WhnfI (term : Expr) (initD : LocalContext) (initI : LocalInstances) : MetaM Expr := do
  withReader (fun ctx => {ctx with lctx := initD, localInstances := initI}) do
    whnfI term

@[inline]
def WhnfR (term : Expr) (initD : LocalContext) (initI : LocalInstances) : MetaM Expr := do
  withReader (fun ctx => {ctx with lctx := initD, localInstances := initI}) do
    whnfR term

/-- Note : Affects `Cache` in `Meta.State`, which will not be reset ...-/
@[inline]
def SynthInstance (type : Expr) (initD : LocalContext) (initI : LocalInstances) : MetaM (Option Expr) := do
  let initI := initI.filter (fun x => !x.fvar.fvarId!.isWorker)
  -- ↑ is a patch, avoid it in rewrite
  withReader (fun ctx => {ctx with lctx := initD, localInstances := initI}) do
    try synthInstance type
    catch _ => return .none


@[inline]
def IsTypeCorrect (type : Expr) (initD : LocalContext) (initI : LocalInstances) : MetaM Bool := do
  withReader (fun ctx => {ctx with lctx := initD, localInstances := initI}) do
    isTypeCorrect type

@[inline]
def IsProof (type : Expr) (initD : LocalContext) (initI : LocalInstances) : MetaM Bool := do
  withReader (fun ctx => {ctx with lctx := initD, localInstances := initI}) do
    isProof type

@[inline]
def IsProp (type : Expr) (initD : LocalContext) (initI : LocalInstances) : MetaM Bool := do
  withReader (fun ctx => {ctx with lctx := initD, localInstances := initI}) do
    isProp type

@[inline]
def IsClass? (type : Expr) (initD : LocalContext) (initI : LocalInstances) : MetaM (Option Name) := do
  withReader (fun ctx => {ctx with lctx := initD, localInstances := initI}) do
    isClass? type

@[inline]
def PpExpr (type : Expr) (initD : LocalContext) (initI : LocalInstances) : MetaM Format := do
  withReader (fun ctx => {ctx with lctx := initD, localInstances := initI}) do
    ppExpr type


@[inline]
def WhnfForall (type : Expr) (initD : LocalContext) (initI : LocalInstances) : MetaM Expr := do
  withReader (fun ctx => {ctx with lctx := initD, localInstances := initI}) do
    whnfForall type

private def getTypeBody (type : Expr) (x : Expr) : MetaM (Option Expr) := do
  let type ← whnfForall type
  match type with
  | Expr.forallE _ _ b _ => return (.some (b.instantiate1 x))
  | _                    => return .none

@[inline]
def GetTypeBody (type : Expr) (x : Expr) (initD : LocalContext) (initI : LocalInstances) : MetaM (Option Expr) := do
  withReader (fun ctx => {ctx with lctx := initD, localInstances := initI}) do
    getTypeBody type x


@[inline]
def Lean.FVarId.GetValue? (fv : FVarId) (initD : LocalContext) (initI : LocalInstances) : MetaM (Option Expr) := do
  withReader (fun ctx => {ctx with lctx := initD, localInstances := initI}) do
    getValue? fv

--
