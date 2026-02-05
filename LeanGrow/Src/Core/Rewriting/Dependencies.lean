
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Utils.Lean.Expr.Basic
import LeanGrow.Src.Core.Rewriting.Directions

open Lean Meta

@[inline]
partial def getNextBoundedTerm
  (l1 : LocalContext) (l2 : LocalInstances)
  (currentDepth nextDepth : Nat) (dirs : rwDirs) (ref : Expr)
  : MetaM (Prod4 rwDirs Expr LocalContext LocalInstances) := do
  let rec last (l1 : LocalContext) (l2 : LocalInstances) : ListProd rwDirs Expr → MetaM (Prod4 rwDirs Expr LocalContext LocalInstances)
    | .nil => throwError "[getNextBoundedTerm] (2) expected bounded term to be found ..."
    | .cons dirs e more => do
        match dirs, e with
        | _, .mdata _ e =>  last l1 l2 <| .cons dirs e more
        | .ap l r, .app L R =>
            last l1 l2 <| .cons  l L <| .cons  r R more
        | .la .., .lam .. | .al .., .forallE .. | .le .., .letE .. => return ⟨dirs,e,l1,l2⟩
        | .pro r, .proj _ _ R => last l1 l2 <| .cons r R more
        | _, _ => last l1 l2 more
  let rec go (l1 : LocalContext) (l2 : LocalInstances) : ListProd3 Nat rwDirs Expr → MetaM (Prod4 rwDirs Expr LocalContext LocalInstances)
    | .nil => throwError "[getNextBoundedTerm] (1) expected bounded term to be found ..."
    | .cons depth dirs e more =>
        if depth == nextDepth
        then
          last l1 l2 <| .cons dirs e .nil
        else
          match dirs, e with
          | _, .mdata _ e => go l1 l2 <| .cons depth dirs e more
          | .ap l r, .app L R =>
              go l1 l2 <| .cons depth l L <| .cons depth r R more
          | .la _ r, .lam _ L R _ | .al _ r, .forallE _ L R _ => do
              let w ← worker depth
              let ⟨_,R,l1,l2⟩ ← withFreeing w L R l1 l2
              go l1 l2 <| .cons (depth+1) r R more
          | .le _ _ r, .letE _ T V R _ => do
              -- if depth isn't next, pattern can't be in binding type or let-val
              let w ← worker depth
              let ⟨_,R,l1,l2⟩ ← withFreeingLet w T V R l1 l2
              go l1 l2 <| .cons (depth+1) r R more
          | .pro r, .proj _ _ R => go l1 l2 <| .cons depth r R more
          | _, _ => -- cover .yes/.no, we don't throw error if complete mismatch
              go l1 l2 more
  go l1 l2 <| .cons currentDepth dirs ref .nil

#check 1

/-- Replaces the dirs corresponding to occurences of `suppat` with .yes-/
@[inline]
def replaceDirsAtSupPattern (dirs : rwDirs) (ref suppat : Expr) : rwDirs :=
  let rec go : rwDirs → Expr → rwDirs
    | d, .mdata _ e => go d e
    | .la l r, e@(.lam _ L R _) =>
        if e == suppat
        then .yes
        else
          match (go l L), (go r R) with
          | .no, .no => .no
          | rl, rr => .la rl rr
    | .al l r, e@(.forallE _ L R _) =>
        if e == suppat
        then .yes
        else
          match (go l L), (go r R) with
          | .no, .no => .no
          | rl, rr => .al rl rr
    | .le l r z, e@(.letE _ L R Z _) =>
        if e == suppat
        then .yes
        else
          match (go l L), (go r R), (go z Z) with
          | .no, .no, .no => .no
          | rl, rr, rz => .le rl rr rz
    | .ap l r, .app L R =>
        match (go l L), (go r R) with
          | .no, .no => .no
          | rl, rr => .ap rl rr
    | .pro l, .proj _ _ L =>
        match (go l L) with
        | .no => .no
        | rl => .pro rl
    -- We don't expect .yes since `dirs` referd to a pattern in `suppat`
    | _, _ => .no
  go dirs ref

#check 1

/-- We expect transitive dependencies to be found by revert !-/
partial def Lean.Expr.getGUFVarsIdsWithDirectDeps
  (l1 : LocalContext) (l2 : LocalInstances)
  (knownDeps knownIndeps : List FVarId) (pat e : Expr)
  : MetaM (Prod3 (List FVarId × List FVarId) LocalContext LocalInstances) := do
    e.onAllSubtermsFoldNoPartialM l1 l2
      ((knownDeps, knownIndeps) : List FVarId × List FVarId)
      (fun x _ _ s@(sofarD,sofarI) l1 l2 =>
        match x with
        | .fvar y@⟨.num k _⟩ => do
          if sofarI.contains y
          then return ⟨s,l1,l2⟩
          else
            if k == `g
            then
              let T ← y.getType
              let .mk h? l1 l2 ← Expr.hasPatternTR! l1 l2 pat T
              if h?
              then
                return ⟨(sofarD.insert y, sofarI),l1,l2⟩
              else
                return ⟨(sofarD, sofarI.insert y),l1,l2⟩
            else
              if k == `u
              then
                match (← y.getDecl) with
                | .ldecl _ _ _  T V .. =>
                    let .mk h? l1 l2 ← Expr.hasPatternTR! l1 l2 pat T
                    if h?
                    then
                      -- we effictivly unfold the unode to get the real dependecies
                      let ⟨(sofarD, sofarI),l1,l2⟩ ← Expr.getGUFVarsIdsWithDirectDeps l1 l2 sofarD sofarI pat V
                      return ⟨(sofarD.insert y, sofarI),l1,l2⟩
                    else
                      return ⟨(sofarD, sofarI.insert y),l1,l2⟩
                | _ => throwError s!"[getGUFVarsIdsWithDirectDeps] unode that's not a local decl ?!? id {repr y}"
              else
                return ⟨s,l1,l2⟩
        | _ => return ⟨s,l1,l2⟩
        ) --<| fun res => k res.1 res.2

#check 1

partial def getDeps
  (l1 : LocalContext) (l2 : LocalInstances)
  (dirs : rwDirs) (ref : Expr) (pat : Expr) (d : Nat)
  : MetaM (Prod3 (List FVarId) LocalContext LocalInstances) :=
  do
  mtracing
  let rec inner
    (l1 : LocalContext) (l2 : LocalInstances)
    (hdep : Array ParamInfo) (asd : Array rwDirs) (as : Array Expr)
    (p : Nat) (depsPos : List Nat) (todo : ListProd3 Nat rwDirs Expr) (rev skip : List FVarId)
    : MetaM (Prod5 (List FVarId) (List FVarId) (ListProd3 Nat rwDirs Expr) LocalContext LocalInstances) := do
      if p < as.size
      then
        let pinfo := hdep[p]!
        if pinfo.backDeps.any (fun x => depsPos.contains x)
        then
          let dhere := asd[p]!
          if dhere != .no
          then
            -- depends on rewritten pattern and contains rewritten pattern: investigate further
            let todo := .cons d dhere as[p]! todo
            inner l1 l2 hdep asd as (p+1) (p :: depsPos) todo rev skip
          else
            -- arg depends on a term that was rewritten, but doesn't contain pattern
            -- unless "split", we assume an fvar is to blame, and we should revert it
            let ⟨(rev,skip),l1,l2⟩ ← Expr.getGUFVarsIdsWithDirectDeps l1 l2 rev skip pat as[p]!
            inner l1 l2 hdep asd as (p+1) (p :: depsPos) todo rev skip
        else
          -- arg doesn't depend on a pattern that was rewritten
          let dhere := asd[p]!
          if dhere != .no
          then
            -- doesn't depend and contains rewritten pattern: investigate further
            let todo := .cons d dhere as[p]! todo
            inner l1 l2 hdep asd as (p+1) (p :: depsPos) todo rev skip
          else
            -- and doesn't contain pattern : ignore it completely
            inner l1 l2 hdep asd as (p+1) depsPos todo rev skip
      else
        return ⟨rev,skip,todo,l1,l2⟩
  let rec go (l1 : LocalContext) (l2 : LocalInstances) (kd ki : List FVarId) : ListProd3 Nat rwDirs Expr → MetaM (Prod3 (List FVarId) LocalContext LocalInstances)
    | .nil => return ⟨kd,l1,l2⟩
    | .cons d dirs ref more => do
        match dirs with
        | .no | .yes => go l1 l2 kd ki more
        | .la l r =>
          match ref with
          | .mdata _ ref => go l1 l2 kd ki <| .cons d dirs ref more
          | .lam _ L R _ => do
              let w ← worker d
              let ⟨_,R,l1,l2⟩ ← withFreeing w L R l1 l2
              go l1 l2 kd ki <| .cons d l L <| .cons (d+1) r R more
          | _ => throwError s!"[getDeps] dirs and expr mismatch: {repr dirs} vs. {← ppExpr ref}"
        | .al l r =>
          match ref with
          | .mdata _ ref => go l1 l2 kd ki <| .cons d dirs ref more
          | .forallE _ L R _ => do
              let w ← worker d
              let ⟨_,R,l1,l2⟩ ← withFreeing w L R l1 l2
              go l1 l2 kd ki <| .cons d l L <| .cons (d+1) r R more
          | _ => throwError s!"[getDeps] dirs and expr mismatch: {repr dirs} vs. {← ppExpr ref}"
        | .le l r z =>
          match ref with
          | .mdata _ ref => go l1 l2 kd ki <| .cons d dirs ref more
          | .letE _ L R Z _ => do
              let w ← worker d
              let ⟨_,Z,l1,l2⟩ ← withFreeingLet w L R Z l1 l2
              go l1 l2 kd ki <| .cons d l L <| .cons d r R <| .cons (d+1) z Z more
          | _ => throwError s!"[getDeps] dirs and expr mismatch: {repr dirs} vs. {← ppExpr ref}"
        | o@(.pro dirs) =>
          match ref with
          | .mdata _ ref => go l1 l2 kd ki <| .cons d o ref more
          | .proj _ _ ref => go l1 l2 kd ki <| .cons d dirs ref more
          | _ => throwError s!"[getDeps] dirs and expr mismatch: {repr dirs} vs. {← ppExpr ref}"
        | .ap .. =>
          match ref with
          | .mdata _ ref => go l1 l2 kd ki <| .cons d dirs ref more
          | .app .. => do
              withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
                let ⟨h,_,as,asd⟩ := dirs.getAppFnArgs ref
                mtrace on .zero with s!"[getDeps] h {← ppExpr h}"
                mtrace on .zero with s!"[getDeps] as {← as.mapM ppExpr}"
                mtrace on .zero with s!"[getDeps] asd {repr asd}"
                let hdep ← getFunInfo h
                let hdep := hdep.paramInfo
                /- Head deps shoud be irrelevant : if app as arg in app has its ouput type affected,
                hen we already handled it and its dependecies as an arg. -/
                let ⟨rev,skip,todo,l1,l2⟩ ← inner l1 l2 hdep asd as 0 [] more kd ki
                go l1 l2 rev skip todo
          | _ => throwError s!"[getDeps] dirs and expr mismatch: {repr dirs} vs. {← ppExpr ref}"
  go l1 l2 [] [] <| .cons d dirs ref .nil
