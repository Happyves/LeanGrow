
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Batteries.Tactic.OpenPrivate
import Lean.Meta.Tactic.Grind.RevertAll
import LeanGrow.Src.Utils.Lean.Expr.Basic

open Lean Meta

-- **Note** the code is based on:
#check MVarId.revert

open private Lean.MetavarContext.MkBinding.getLocalDeclWithSmallestIdx from Lean.MetavarContext
open private Lean.MetavarContext.MkBinding.withFreshCache from Lean.MetavarContext
open private Lean.MetavarContext.MkBinding.mkFreshBinderName from Lean.MetavarContext
open private Lean.MetavarContext.MkBinding.getInScope from Lean.MetavarContext
open private Lean.MetavarContext.MkBinding.mkMVarApp from Lean.MetavarContext


@[specialize introAdmissible?]
def collectForwardDeps_NoTn_1 (lctx : LocalContext) (introAdmissible? : Nat → Bool) (toRevert : Array Expr) : MetavarContext.MkBinding.M (Array Expr) := do
  if toRevert.size == 0 then
    pure toRevert
  else
    let newToRevert      := toRevert
    let firstDeclToVisit := Lean.MetavarContext.MkBinding.getLocalDeclWithSmallestIdx lctx toRevert
    let initSize         := newToRevert.size
    -- For all local context decl (over Persistent array)
    lctx.foldlM (init := newToRevert) (start := firstDeclToVisit.index) fun (newToRevert : Array Expr) decl => do
      match decl.fvarId.name with
      | .num (.num _ _) _ => return newToRevert
      | .num (.str _ k) i =>
          if k == "w"
          then
            if initSize.any fun i _ => decl.fvarId == newToRevert[i]!.fvarId! then
              return newToRevert
            -- if among original, skip
            else  if (← findLocalDeclDependsOn decl (newToRevert.any fun x => x.fvarId! == ·)) then
                    return newToRevert.push decl.toExpr
                  else
                    return newToRevert
          else
            if introAdmissible? i
            then
              if initSize.any fun i _ => decl.fvarId == newToRevert[i]!.fvarId! then
                return newToRevert
              -- if among original, skip
              else  if (← findLocalDeclDependsOn decl (newToRevert.any fun x => x.fvarId! == ·)) then
                      return newToRevert.push decl.toExpr
                    else
                      return newToRevert
            else
                      return newToRevert
      | _ => -- for testing only
          if initSize.any fun i _ => decl.fvarId == newToRevert[i]!.fvarId! then
            return newToRevert
          -- if among original, skip
          else  if (← findLocalDeclDependsOn decl (newToRevert.any fun x => x.fvarId! == ·)) then
                  return newToRevert.push decl.toExpr
                else
                  return newToRevert


@[inline, specialize introAdmissible?]
def collectForwardDeps_NoTn_2 (introAdmissible? : Nat → Bool) (toRevert : Array Expr) : MetavarContext.MkBindingM (Array Expr) := fun ctx =>
  collectForwardDeps_NoTn_1 ctx.lctx introAdmissible? toRevert { preserveOrder := true, mainModule := ctx.mainModule }

@[inline, specialize introAdmissible?]
def collectForwardDeps_NoTn_3 (introAdmissible? : Nat → Bool) (toRevert : Array Expr): MetaM (Array Expr) := do
  liftMkBindingM <| collectForwardDeps_NoTn_2 introAdmissible? toRevert

-- open MetavarContext MkBinding

mutual

  private partial def visit (xs : Array Expr) (e : Expr) : Lean.MetavarContext.MkBinding.M Expr :=
    if !e.hasMVar then pure e else checkCache { val := e : ExprStructEq } fun _ => elim xs e

  private partial def elim (xs : Array Expr) (e : Expr) : Lean.MetavarContext.MkBinding.M Expr :=
    match e with
    | .proj _ _ s      => return e.updateProj! (← visit xs s)
    | .forallE _ d b _ => return e.updateForallE! (← visit xs d) (← visit xs b)
    | .lam _ d b _     => return e.updateLambdaE! (← visit xs d) (← visit xs b)
    | .letE _ t v b dep  => return e.updateLet! (← visit xs t) (← visit xs v) (← visit xs b) dep
    | .mdata _ b       => return e.updateMData! (← visit xs b)
    | .app ..          => e.withApp fun f args => elimApp xs f args
    | .mvar _          => elimApp xs e #[]
    | e                => return e

  /--
    Given a metavariable with type `e`, kind `kind` and free/meta variables `xs` in its local context `lctx`,
    create the type for a new auxiliary metavariable. These auxiliary metavariables are created by `elimMVar`.

    See "Gruesome details" section in the beginning of the file.

    Note: It is assumed that `xs` is the result of calling `collectForwardDeps` on a subset of variables in `lctx`.
  -/
  private partial def mkAuxMVarType (lctx : LocalContext) (xs : Array Expr) (kind : MetavarKind) (e : Expr) : Lean.MetavarContext.MkBinding.M Expr := do
    let e ← abstractRangeAux xs xs.size e
    xs.size.foldRevM (init := e) fun i _ e => do
      let x := xs[i]
      if x.isFVar then
        match lctx.getFVar! x with
        | LocalDecl.cdecl _ _ n type bi _ =>
          let type := type.headBeta
          let type ← abstractRangeAux xs i type
          return Lean.mkForall n bi type e
        | LocalDecl.ldecl _ _ n type value nonDep _ =>
            let type := type.headBeta
            let type  ← abstractRangeAux xs i type
            let value ← abstractRangeAux xs i value
            let e := mkLet n type value e nonDep
            match kind with
            | MetavarKind.syntheticOpaque =>
              -- See "Gruesome details" section in the beginning of the file
              let e := e.liftLooseBVars 0 1
              return mkForall n BinderInfo.default type e
            | _ => pure e
      else
        -- `xs` may contain metavariables as "may dependencies" (see `findExprDependsOn`)
        let mvarDecl := (← get).mctx.getDecl x.mvarId!
        let type := mvarDecl.type.headBeta
        let type ← abstractRangeAux xs i type
        let id ← if mvarDecl.userName.isAnonymous then Lean.MetavarContext.MkBinding.mkFreshBinderName else pure mvarDecl.userName
        return Lean.mkForall id (← read).binderInfoForMVars type e
  where
    abstractRangeAux (xs : Array Expr) (i : Nat) (e : Expr) : Lean.MetavarContext.MkBinding.M Expr := do
      let e ← elim xs e
      pure (e.abstractRange i xs)

  /--
    "Eliminate" the given variables `xs` from the context of the metavariable represented `mvarId`
    by returning the application of a new metavariable whose type abstracts the forward dependencies
    on `xs` after restricting it to the free variables in the local context of `mvarId`.

    See details in the comment at the top of the file.
  -/
  private partial def elimMVar (xs : Array Expr) (mvarId : MVarId) (args : Array Expr) : Lean.MetavarContext.MkBinding.M (Expr × Array Expr) := do
    let mvarDecl  := (← getMCtx).getDecl mvarId
    let mvarLCtx  := mvarDecl.lctx
    --let toRevert  := Lean.MetavarContext.MkBinding.getInScope mvarLCtx xs
    -- **LeanGrow** all fvars are in scope and we only expect fvars, so ↑ is useless here
    let toRevert  := xs
    if toRevert.size == 0 then
      let args ← args.mapM (visit xs)
      return (mkAppN (mkMVar mvarId) args, #[])
    else
      /- `newMVarKind` is the kind for the new auxiliary metavariable.
          There is an alternative approach where we use
          ```
          let newMVarKind := if !mctx.isAssignable mvarId || mvarDecl.isSyntheticOpaque then MetavarKind.syntheticOpaque else MetavarKind.natural
          ```
          In this approach, we use the natural kind for the new auxiliary metavariable if the original metavariable is synthetic and assignable.
          Since we mainly use synthetic metavariables for pending type class (TC) resolution problems,
          this approach may minimize the number of TC resolution problems that may need to be resolved.
          A potential disadvantage is that `isDefEq` will not eagerly use `synthPending` for natural metavariables.
          That being said, we should try this approach as soon as we have an extensive test suite.
      -/
      let newMVarKind := if !(← mvarId.isAssignable) then MetavarKind.syntheticOpaque else mvarDecl.kind
      let args ← args.mapM (visit xs)
      -- Note that `toRevert` only contains free variables at this point since it is the result of `getInScope`;
      -- after `collectForwardDeps`, this may no longer be the case because it may include metavariables
      -- whose local contexts depend on `toRevert` (i.e. "may dependencies")
      -- **LeanGrow** unless I'm mistaken, `xs` will correspond to the `toRevert` of `Lean.MVarId.revert_NoTn`, so dependencies have already been computed
      -- let toRevert ← collectForwardDeps_NoTn_1 mvarLCtx toRevert
      /- **LeanGrow** we don't update local contexts as is done in standard revert, where we want to discard the "old".
      This is pointless in LeanGrow, as we work with Meta.Context and not the MvarDecl contexts.
      -/
      let newMVarLCtx   := Lean.MetavarContext.MkBinding.reduceLocalContext mvarLCtx toRevert
      let newLocalInsts := mvarDecl.localInstances.filter fun inst => toRevert.all fun x => inst.fvar != x
      -- Remark: we must reset the cache before processing `mkAuxMVarType` because `toRevert` may not be equal to `xs`
      let newMVarType ← Lean.MetavarContext.MkBinding.withFreshCache do mkAuxMVarType mvarLCtx toRevert newMVarKind mvarDecl.type
      let newMVarId    := { name := (← get).ngen.curr }
      let newMVar      := mkMVar newMVarId
      let result       :=  Lean.MetavarContext.MkBinding.mkMVarApp mvarLCtx newMVar toRevert newMVarKind
      let numScopeArgs := mvarDecl.numScopeArgs + result.getAppNumArgs
      modify fun s => { s with
          mctx := s.mctx.addExprMVarDecl newMVarId Name.anonymous newMVarLCtx newLocalInsts newMVarType newMVarKind numScopeArgs,
          ngen := s.ngen.next
        }
      if !mvarDecl.kind.isSyntheticOpaque then
        mvarId.assign result
      else
        /- If `mvarId` is the lhs of a delayed assignment `?m #[x_1, ... x_n] := ?mvarPending`,
           then `nestedFVars` is `#[x_1, ..., x_n]`.
           In this case, `newMVarId` is also `syntheticOpaque` and we add the delayed assignment delayed assignment
           ```
           ?newMVar #[y_1, ..., y_m, x_1, ... x_n] := ?m
           ```
           where `#[y_1, ..., y_m]` is `toRevert` after `collectForwardDeps`.
        -/
        let (mvarIdPending, nestedFVars) ← match (← getDelayedMVarAssignment? mvarId) with
          | none => pure (mvarId, #[])
          | some { fvars, mvarIdPending } => pure (mvarIdPending, fvars)
        assignDelayedMVar newMVarId (toRevert ++ nestedFVars) mvarIdPending
      return (mkAppN result args, toRevert)

  private partial def elimApp (xs : Array Expr) (f : Expr) (args : Array Expr) : Lean.MetavarContext.MkBinding.M Expr := do
    match f with
    | Expr.mvar mvarId =>
      match (← getExprMVarAssignment? mvarId) with
      | some newF =>
        if newF.isLambda then
          let args ← args.mapM (visit xs)
          /- Arguments in `args` can become irrelevant after we beta reduce. -/
          elim xs <| newF.betaRev args.reverse
        else
          elimApp xs newF args
      | none =>
        if (← read).mvarIdsToAbstract.contains mvarId then
          return mkAppN f (← args.mapM (visit xs))
        else
          -- We set `usedLetOnly := true` to avoid unnecessary let binders in the new metavariable type.
          return (← elimMVar xs mvarId args).1
    | _ =>
      return mkAppN (← visit xs f) (← args.mapM (visit xs))

end

partial def revert_NoTn_1 (xs : Array Expr) (mvarId : MVarId) : Lean.MetavarContext.MkBinding.M (Expr × Array Expr) :=
  Lean.MetavarContext.MkBinding.withFreshCache do
    -- We set `usedLetOnly := false`, because in the `revert` tactic
    -- we expect that reverting a let variable always results in a let binder.
    elimMVar xs mvarId #[]

def revert_NoTn_2 (xs : Array Expr) (mvarId : MVarId) : Lean.MetavarContext.MkBindingM (Expr × Array Expr) := fun ctx =>
  revert_NoTn_1 xs mvarId { preserveOrder := true, mainModule := ctx.mainModule }



/-
- Expects `fvarIds` to be ordered wrt. dependencies (implementation follows revert with preserveOrder := true)
- Will revert auxiliary declarations of local context (so does `MVarId.revertAll`)
- doesn't load mvar context, so expects all relevant vars in `Meta.Context`
-/
@[specialize introAdmissible?]
def Lean.MVarId.revert_NoTn (introAdmissible? : Nat → Bool)
  (l1 : LocalContext) (l2 : LocalInstances)
  (mvarId : MVarId) (fvarIds : Array FVarId) : MetaM (Array FVarId × MVarId) :=
  withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
    if fvarIds.isEmpty then
      pure (#[], mvarId)
    else
      let fvars := fvarIds.map mkFVar
      let toRevert ← collectForwardDeps_NoTn_3 introAdmissible? fvars
      /- We should clear any `auxDecl` in `toRevert` -/
      let mut toRevertNew := #[]
      for x in toRevert do
        if (← x.fvarId!.getDecl).isAuxDecl then
          continue
        else
          toRevertNew := toRevertNew.push x
      -- TODO: the following code can be optimized because `MetavarContext.revert` will compute `collectDeps` again.
      -- We should factor out the relevant part

      -- Set metavariable kind to natural to make sure `revert` will assign it.
      mvarId.setKind .natural
      let (e, toRevert) ←
        try
          liftMkBindingM <| revert_NoTn_2 toRevertNew mvarId
        finally
          mvarId.setKind .syntheticOpaque
      let mvar := e.getAppFn
      mvar.mvarId!.setKind .syntheticOpaque
      return (toRevert.map Expr.fvarId!, mvar.mvarId!)



@[specialize introAdmissible?]
def collectForwardDeps_NoTn_1' (lctx : LocalContext) (introAdmissible? : Nat → Bool) (toRevert : Array Expr) (sinkRevCutOff : Nat) : MetavarContext.MkBinding.M (Array Expr) := do
  if toRevert.size == 0 then
    pure toRevert
  else
    let newToRevert      := toRevert
    let firstDeclToVisit := Lean.MetavarContext.MkBinding.getLocalDeclWithSmallestIdx lctx toRevert
    let initSize         := newToRevert.size
    -- For all local context decl (over Persistent array)
    let (safeToRev,sinks) ←
      lctx.foldlM (init := (newToRevert, [])) (start := firstDeclToVisit.index) fun ((newToRevert : Array Expr), (sinks : List Expr)) decl => do
        match decl.fvarId.name with
        | .num (.num _ _) _ => return (newToRevert,sinks)
        | .num (.str _ k) i =>
          if k == "w"
          then
            if initSize.any fun i _ => decl.fvarId == newToRevert[i]!.fvarId! then
              return (newToRevert,sinks)
            else
              let decE := decl.toExpr
              let decT := decl.type
              let decFvs := decT.getFVars
              match sinks.filter (fun x => decFvs.contains x) with
              | inter@(_ :: _) =>
                  let sinks := decE :: (sinks.removeAll inter)
                  let newToRevert := newToRevert ++ inter
                  return (newToRevert,sinks)
              | [] =>
                  if newToRevert.any (fun x => decFvs.contains x)
                  then
                    let sinks := decE :: sinks
                    return (newToRevert,sinks)
                  else
                    return (newToRevert,sinks)
          else
            if introAdmissible? i
            then
              if initSize.any fun i _ => decl.fvarId == newToRevert[i]!.fvarId! then
                return (newToRevert,sinks)
              else
                let decE := decl.toExpr
                let decT := decl.type
                let decFvs := decT.getFVars
                match sinks.filter (fun x => decFvs.contains x) with
                | inter@(_ :: _) =>
                    let sinks := decE :: (sinks.removeAll inter)
                    let newToRevert := newToRevert ++ inter
                    return (newToRevert,sinks)
                | [] =>
                    if newToRevert.any (fun x => decFvs.contains x)
                    then
                      let sinks := decE :: sinks
                      return (newToRevert,sinks)
                    else
                      return (newToRevert,sinks)
            else return (newToRevert,sinks)
        | _ => --for testing only
          if initSize.any fun i _ => decl.fvarId == newToRevert[i]!.fvarId! then
              return (newToRevert,sinks)
            else
              let decE := decl.toExpr
              let decT := decl.type
              let decFvs := decT.getFVars
              match sinks.filter (fun x => decFvs.contains x) with
              | inter@(_ :: _) =>
                  let sinks := decE :: (sinks.removeAll inter)
                  let newToRevert := newToRevert ++ inter
                  return (newToRevert,sinks)
              | [] =>
                  if newToRevert.any (fun x => decFvs.contains x)
                  then
                    let sinks := decE :: sinks
                    return (newToRevert,sinks)
                  else
                    return (newToRevert,sinks)
    return safeToRev ++ (sinks.take sinkRevCutOff).toArray



@[inline, specialize introAdmissible?]
def collectForwardDeps_NoTn_2' (introAdmissible? : Nat → Bool) (toRevert : Array Expr) (sinkRevCutOff : Nat) : MetavarContext.MkBindingM (Array Expr) := fun ctx =>
  collectForwardDeps_NoTn_1' ctx.lctx introAdmissible? toRevert sinkRevCutOff { preserveOrder := true, mainModule := ctx.mainModule }

@[inline, specialize introAdmissible?]
def collectForwardDeps_NoTn_3' (introAdmissible? : Nat → Bool) (toRevert : Array Expr) (sinkRevCutOff : Nat): MetaM (Array Expr) := do
  liftMkBindingM <| collectForwardDeps_NoTn_2' introAdmissible? toRevert sinkRevCutOff



/-
- Expects `fvarIds` to be ordered wrt. dependencies (implementation follows revert with preserveOrder := true)
- Will revert auxiliary declarations of local context (so does `MVarId.revertAll`)
- doesn't load mvar context, so expects all relevant vars in `Meta.Context`

When collecting dependencies, we consider sinks to be dependecies with no further dependencies.
For example, if we want to revert `n : Nat` and our context has `x : Fin n` and `h : x.val = 42`,
the all will be reverted, and `h` is the only sink.
In this version of revert, we only revert non-sink fvars, and the last `sinkRevCutOff` sink fvars.
The reason is that in LeanGrow, since we never delete forward-facts, we expect the number of sinks
of Type-types fvars to grow. The method we develop here is ertainly unsafe, as we risk not reverting
the relevant assumptions due to them being "old", but it should be a good tradeoff for performance.
-/
@[specialize introAdmissible?]
def Lean.MVarId.revert_NoTn_cutOff (introAdmissible? : Nat → Bool)
  (l1 : LocalContext) (l2 : LocalInstances)
  (mvarId : MVarId) (fvarIds : Array FVarId) (sinkRevCutOff : Nat) : MetaM (Array FVarId × MVarId) :=
  withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
    if fvarIds.isEmpty then
      pure (#[], mvarId)
    else
      let fvars := fvarIds.map mkFVar
      let toRevert ← collectForwardDeps_NoTn_3' introAdmissible? fvars sinkRevCutOff
      /- We should clear any `auxDecl` in `toRevert` -/
      let mut toRevertNew := #[]
      for x in toRevert do
        if (← x.fvarId!.getDecl).isAuxDecl then
          continue
        else
          toRevertNew := toRevertNew.push x
      -- TODO: the following code can be optimized because `MetavarContext.revert` will compute `collectDeps` again.
      -- We should factor out the relevant part

      -- Set metavariable kind to natural to make sure `revert` will assign it.
      mvarId.setKind .natural
      let (e, toRevert) ←
        try
          liftMkBindingM <| revert_NoTn_2 toRevertNew mvarId
        finally
          mvarId.setKind .syntheticOpaque
      let mvar := e.getAppFn
      mvar.mvarId!.setKind .syntheticOpaque
      return (toRevert.map Expr.fvarId!, mvar.mvarId!)


/-- Recall `depsCache` is forward deps and `workerDepsCache` is backward deps-/
@[specialize introAdmissible?]
partial def findDepsWiCut
  (introAdmissible? : Nat → Bool) (depsCache  : Array (List LocalDecl))
  (workerDepsCache : Array (FVarId × (List LocalDecl))) (RevCutOff : Nat)
  (init : List LocalDecl) : MetaM (Array LocalDecl) :=
  let rec go (done : Array LocalDecl) : List LocalDecl → (Array LocalDecl)
    | [] => done
    | x :: xs =>
      trace set TracingFlags.none in
      match x.fvarId.name with
      | .num (.str _ k) i =>
          trace on .one with s!"[revert_NoTn_cutOff_wDepsCache][findDepsWiCut] looking at ugnode {i}" in
          if k == "w"
          then
            if (done.binSearchContains x (fun x y => x.index < y.index))
            then
              trace on .one with s!"[revert_NoTn_cutOff_wDepsCache][findDepsWiCut] {i} admissble, but already contained" in
              go done xs
            else
              trace on .one with s!"[revert_NoTn_cutOff_wDepsCache][findDepsWiCut] inserting {i}" in
              go (done.binInsert (fun x y => x.index < y.index) x) (xs)
          else
            if introAdmissible? i
            then
              if (done.binSearchContains x (fun x y => x.index < y.index))
              then
                trace on .one with s!"[revert_NoTn_cutOff_wDepsCache][findDepsWiCut] {i} admissble, but already contained" in
                go done xs
              else
                let dx := (depsCache[i]!).take RevCutOff
                trace on .one with s!"[revert_NoTn_cutOff_wDepsCache][findDepsWiCut] inserting {i}, adding {repr <| dx.map LocalDecl.fvarId}" in
                go (done.binInsert (fun x y => x.index < y.index) x) (dx ++ xs)
            else
              trace on .one with s!"[revert_NoTn_cutOff_wDepsCache][findDepsWiCut] {i} inadmisible" in
              go done xs
      | _ => go done xs
  let std := go #[] init
  do
  let (res,_) ← workerDepsCache.foldlM (fun (R,i) (wfid,wd) => do
    let dec ← wfid.getDecl
    if @Array.contains _ ⟨fun x y => x.fvarId == y.fvarId⟩ R dec
    then
      return (R,i+1)
    else
      if wd.any (fun x => @Array.contains _ ⟨fun x y => x.fvarId == y.fvarId⟩ R x)
      then
        return (R.push dec,i+1) -- fvars can't depend on loose bvars, so we may append the latter to the end
      else
        return (R,i+1)
    ) (std,0)
  return res



/-- Recall `depsCache` is forward deps and `workerDepsCache` is backward deps-/
@[specialize introAdmissible?]
partial def findDeps
  (introAdmissible? : Nat → Bool) (depsCache : Array (List LocalDecl))
  (workerDepsCache : Array (FVarId × (List LocalDecl)))
  (init : List LocalDecl) : MetaM (Array LocalDecl) :=
  let rec go (done : Array LocalDecl) : List LocalDecl → (Array LocalDecl)
    | [] => done
    | x :: xs =>
      trace set TracingFlags.none in
      match x.fvarId.name with
      | .num (.str _ k) i =>
          trace on .one with s!"[revert_NoTn_cutOff_wDepsCache][findDeps] looking at ugnode {i}" in
          if k == "w"
          then
            if (done.binSearchContains x (fun x y => x.index < y.index))
            then
              trace on .one with s!"[revert_NoTn_cutOff_wDepsCache][findDeps] {i} admissble, but already contained" in
              go done xs
            else
              trace on .one with s!"[revert_NoTn_cutOff_wDepsCache][findDeps] inserting {i}" in
              go (done.binInsert (fun x y => x.index < y.index) x) (xs)
          else
            if introAdmissible? i
            then
              if (done.binSearchContains x (fun x y => x.index < y.index))
              then
                trace on .one with s!"[revert_NoTn_cutOff_wDepsCache][findDeps] {i} admissble, but already contained" in
                go done xs
              else
                let dx := (depsCache[i]!)
                trace on .one with s!"[revert_NoTn_cutOff_wDepsCache][findDeps] inserting {i}, adding {repr <| dx.map LocalDecl.fvarId}" in
                go (done.binInsert (fun x y => x.index < y.index) x) (dx ++ xs)
            else
              trace on .one with s!"[revert_NoTn_cutOff_wDepsCache][findDeps] {i} inadmisible" in
              go done xs
      | _ => go done xs
  let std := go #[] init
  do
  let (res,_) ← workerDepsCache.foldlM (fun (R,i) (wfid,wd) => do
    let dec ← wfid.getDecl
    if @Array.contains _ ⟨fun x y => x.fvarId == y.fvarId⟩ R dec
    then
      return (R,i+1)
    else
      if wd.any (fun x => @Array.contains _ ⟨fun x y => x.fvarId == y.fvarId⟩ R x)
      then
        return (R.push dec,i+1) -- fvars can't depend on loose bvars, so we may append the latter to the end
      else
        return (R,i+1)
    ) (std,0)
  return res

/-
- Expects `fvarIds` to be ordered wrt. dependencies (implementation follows revert with preserveOrder := true)
- Will revert auxiliary declarations of local context (so does `MVarId.revertAll`)
- doesn't load mvar context, so expects all relevant vars in `Meta.Context`

When collecting dependencies, we consider sinks to be dependecies with no further dependencies.
For example, if we want to revert `n : Nat` and our context has `x : Fin n` and `h : x.val = 42`,
the all will be reverted, and `h` is the only sink.
In this version of revert, we assume the existance of the data `depsCache`, which, given the u-g-index
of the fvar, has as entry at that index the fvars that depend on it, stacked on a list where the first
elements correspond to latest additions. For each of these dependencies, we take the `RevCutOff` last
introduced fvars, to be reverted, to performance reasons (see explanation in `revert_NoTn_cutOff`).
We then merge the dependencies with `Array.binInsert` wrt. the decl index.

**Very important** : we don't expect worker fvars !!!
-/
@[specialize introAdmissible?]
partial def Lean.MVarId.revert_NoTn_cutOff_wDepsCache (introAdmissible? : Nat → Bool)
  (l1 : LocalContext) (l2 : LocalInstances)
  (mvarId : MVarId) (fvarIds : Array FVarId)
  (depsCache : Array (List LocalDecl)) (workerDepsCache : Array (FVarId × (List LocalDecl)))  (RevCutOff : Nat)
  : MetaM (Array FVarId × MVarId) :=
  withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
    if fvarIds.isEmpty then
      pure (#[], mvarId)
    else
      let toRevert0 ← (fvarIds.foldlM (fun I x =>
            match x.name with
            | .num (.str _ k) i => do
                let xd ← x.getDecl
                if k == "w"
                then
                  return xd :: I
                else
                  return xd :: (((depsCache[i]!).take RevCutOff) ++ I)
            | _ =>
                return I)) []
      -- *Note* for structural induction with indices, and functional induction, it's te case that
      -- the fvar that is induced upon is among `fvarIds` but will also be among its indices forward deps,
      -- so we throw them all into `findDeps`, which avoids making duplicates
      let toRevert1 ← findDepsWiCut introAdmissible? depsCache workerDepsCache RevCutOff toRevert0
      let toRevert2 := (toRevert1.map LocalDecl.fvarId).map .fvar
      mtrace on .zero with s!"[revert_NoTn_cutOff_wDepsCache] to revert {toRevert2}"
      mvarId.setKind .natural
      let (e, toRevert) ←
        try
          liftMkBindingM <| revert_NoTn_2 toRevert2 mvarId
        finally
          mvarId.setKind .syntheticOpaque
      let mvar := e.getAppFn
      mvar.mvarId!.setKind .syntheticOpaque
      mtrace on .zero with s!"[revert_NoTn_cutOff_wDepsCache] reverted expr: {← ppExpr e}"
      mtrace on .one with s!"[revert_NoTn_cutOff_wDepsCache] reverted fvars: {toRevert}"
      return (toRevert.map Expr.fvarId!, mvar.mvarId!)



#check sortFVarIds

#check MVarId.revertAll
#check LocalDecl.index

@[specialize introAdmissible?]
partial def Lean.MVarId.revert_NoTn_wDepsCache (introAdmissible? : Nat → Bool)
  (l1 : LocalContext) (l2 : LocalInstances)
  (mvarId : MVarId) (fvarIds : Array FVarId)
  (depsCache : Array (List LocalDecl)) (workerDepsCache : Array (FVarId × (List LocalDecl)))
  : MetaM (Array FVarId × MVarId) :=
  withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
    if fvarIds.isEmpty then
      pure (#[], mvarId)
    else
      let toRevert0 ← (fvarIds.foldlM (fun I x =>
            match x.name with
            | .num (.str _ k) i => do
                let xd ← x.getDecl
                if k == "w"
                then
                  return xd :: I
                else
                  return xd :: (((depsCache[i]!)) ++ I)
            | _ =>
                return I)) []
      -- *Note* for structural induction with indices, and functional induction, it's te case that
      -- the fvar that is induced upon is among `fvarIds` but will also be among its indices forward deps,
      -- so we throw them all into `findDeps`, which avoids making duplicates
      let toRevert1 ← findDeps introAdmissible? depsCache workerDepsCache toRevert0
      let toRevert2 := (toRevert1.map LocalDecl.fvarId).map .fvar
      mtrace on .zero with s!"[revert_NoTn_cutOff_wDepsCache] to revert {toRevert2}"
      mvarId.setKind .natural
      let (e, toRevert) ←
        try
          liftMkBindingM <| revert_NoTn_2 toRevert2 mvarId
        finally
          mvarId.setKind .syntheticOpaque
      let mvar := e.getAppFn
      mvar.mvarId!.setKind .syntheticOpaque
      mtrace on .zero with s!"[revert_NoTn_cutOff_wDepsCache] reverted expr: {← ppExpr e}"
      mtrace on .one with s!"[revert_NoTn_cutOff_wDepsCache] reverted fvars: {toRevert}"
      return (toRevert.map Expr.fvarId!, mvar.mvarId!)
