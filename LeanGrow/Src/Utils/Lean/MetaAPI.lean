

/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Utils.Lean.LocalContext
import LeanGrow.Src.Utils.Lean.MetavarContext

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
      resetDefEqPermCaches
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
      resetDefEqPermCaches
      return .some (rl,re)
    else
      return .none
  catch _ => return .none


namespace CollectMVarsRec

structure State where
  visitedExpr  : ExprSet      := {}
  result       : Array MVarId := .emptyWithCapacity 8

instance : Inhabited State := ⟨{}⟩

mutual
  partial def visit (e : Expr) (s : State) : MetaM State := do
    if !e.hasExprMVar || s.visitedExpr.contains e then return s
    else main e { s with visitedExpr := s.visitedExpr.insert e }

  partial def main (e : Expr) (s : State) : MetaM State := do
    match e with
    | Expr.proj _ _ e      =>
      visit e s
    | Expr.forallE _ d b _ =>
      let s ← visit b s
      visit d s
    | Expr.lam _ d b _     =>
      let s ← visit b s
      visit d s
    | Expr.letE _ t v b _  =>
      let s ← visit t s
      let s ← visit v s
      visit b s
    | Expr.app f a         =>
      let s ← visit a s
      visit f s
    | Expr.mdata _ b       =>
      visit b s
    | Expr.mvar mvarId     =>
      if s.visitedExpr.contains e
      then return s
      else
        let T ← mvarId.getType
        let s ← visit T s
        return { s with result := s.result.push mvarId, visitedExpr := s.visitedExpr.insert e}
    | _                    =>
      return s
end

end CollectMVarsRec

/-- based on `collectMVars` -/
@[inline]
def Lean.Expr.getMVarsRec  (e : Expr) : MetaM (Array MVarId) := do
  let res ← CollectMVarsRec.visit e {}
  return res.result

@[inline]
def Lean.Expr.getMVarsRec' (ini : Array MVarId) (e : Expr) : MetaM (Array MVarId) := do
  let res ← CollectMVarsRec.visit e ⟨{},ini⟩
  return res.result


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
    let mva ← a.getMVarsRec
    let mvb ← b.getMVarsRec' mva
    for mv in mva do
      mv.modifyDecl (fun d => {d with lctx := l1, localInstances := l2})
    for mv in mvb do
      mv.modifyDecl (fun d => {d with lctx := l1, localInstances := l2})
    try
      if ← isExprDefEq a b
      then
        let mc ← getMCtx
        let rl := mc.lAssignment
        let re := mc.eAssignment
        clearMvarAssignments
        for mv in mva do
          mv.modifyDecl (fun d => {d with lctx := {}, localInstances := {}})
        for mv in mvb do
          mv.modifyDecl (fun d => {d with lctx := {}, localInstances := {}})
        resetDefEqPermCaches
        return .some (rl,re)
      else
        for mv in mva do
          mv.modifyDecl (fun d => {d with lctx := {}, localInstances := {}})
        for mv in mvb do
          mv.modifyDecl (fun d => {d with lctx := {}, localInstances := {}})
        resetDefEqPermCaches
        return .none
    catch _ =>
      for mv in mva do
        mv.modifyDecl (fun d => {d with lctx := {}, localInstances := {}})
      for mv in mvb do
        mv.modifyDecl (fun d => {d with lctx := {}, localInstances := {}})
      return .none

@[inline]
def defEqWiMvNoClear (a b : Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (Option (PersistentHashMap LMVarId Level × PersistentHashMap MVarId Expr)) := do
  withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
    let mva ← a.getMVarsRec
    let mvb ← b.getMVarsRec' mva
    for mv in mva do
      mv.modifyDecl (fun d => {d with lctx := l1, localInstances := l2})
    for mv in mvb do
      mv.modifyDecl (fun d => {d with lctx := l1, localInstances := l2})
    try
      if ← isExprDefEq a b
      then
        let mc ← getMCtx
        let rl := mc.lAssignment
        let re := mc.eAssignment
        for mv in mva do
          mv.modifyDecl (fun d => {d with lctx := {}, localInstances := {}})
        for mv in mvb do
          mv.modifyDecl (fun d => {d with lctx := {}, localInstances := {}})
        resetDefEqPermCaches
        return .some (rl,re)
      else
        for mv in mva do
          mv.modifyDecl (fun d => {d with lctx := {}, localInstances := {}})
        for mv in mvb do
          mv.modifyDecl (fun d => {d with lctx := {}, localInstances := {}})
        resetDefEqPermCaches
        return .none
    catch _ =>
      for mv in mva do
        mv.modifyDecl (fun d => {d with lctx := {}, localInstances := {}})
      for mv in mvb do
        mv.modifyDecl (fun d => {d with lctx := {}, localInstances := {}})
      return .none



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

/-- Doesn't load mvars with context, or clears assignments ... -/
@[inline]
def SynthInstance (type : Expr) (initD : LocalContext) (initI : LocalInstances) : MetaM (Option Expr) := do
  withReader (fun ctx => {ctx with lctx := initD, localInstances := initI}) do
    try
      let res ← synthInstance type
      resetSynthInstanceCache
      return .some res
    catch _ =>
      return .none

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


-- # Telescope

private partial def forallMetaTagTelescopeReducingAux
  (tag : String) (lctx : LocalContext) (lins : LocalInstances)
  (e : Expr) (reducing : Bool) (maxMVars? : Option Nat) (kind : MetavarKind) : MetaM (Array Expr × Array BinderInfo × Expr) :=
  process #[] #[] 0 e
where
  process (mvars : Array Expr) (bis : Array BinderInfo) (j : Nat) (type : Expr) : MetaM (Array Expr × Array BinderInfo × Expr) := do
    if maxMVars?.isEqSome mvars.size then
      let type := type.instantiateRevRange j mvars.size mvars;
      return (mvars, bis, type)
    else
      match type with
      | .forallE n d b bi =>
        let d  := d.instantiateRevRange j mvars.size mvars
        let k  := if bi.isInstImplicit then  MetavarKind.synthetic else kind
        let mvar ← mkFreshExprMVarTag tag d lctx lins k n
        let mvars := mvars.push mvar
        let bis   := bis.push bi
        process mvars bis j b
      | _ =>
        let type := type.instantiateRevRange j mvars.size mvars;
        if reducing then do
          let newType ← Whnf type lctx lins
          if newType.isForall then
            process mvars bis mvars.size newType
          else
            return (mvars, bis, type)
        else
          return (mvars, bis, type)

/-- Given `e` of the form `forall ..xs, A`, this combinator will create a new
  metavariable for each `x` in `xs` and instantiate `A` with these.
  Returns a product containing
  - the new metavariables
  - the binder info for the `xs`
  - the instantiated `A`
-/
@[inline]
def ForallMetaTagTelescope (lctx : LocalContext) (lins : LocalInstances) (tag : String) (e : Expr) (kind := MetavarKind.natural) : MetaM (Array Expr × Array BinderInfo × Expr) :=
  forallMetaTagTelescopeReducingAux tag lctx lins e (reducing := false) (maxMVars? := none) kind
