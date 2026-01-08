
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Caching.Formating.Types
import LeanGrow.Src.Utils.LeanGrow.Expr


open Lean Meta



def levelsForCache (module : Name) (thmIdx : Nat) (cinfo : ConstantInfo) : MetaM (Array (LMVarId × Nat) × Nat × Expr) :=
  do
  let now ← getMCtx
  let (mctx,cache,us,num) := cinfo.levelParams.foldl (fun (mctx,lvlA,lvl,i) _ =>
    let lid : LMVarId := ⟨lnode module thmIdx i⟩
    let mctx := mctx.addLevelMVarDecl lid
    let lvlA := lvlA.push (lid, mctx.depth)
    (mctx, lvlA, (.mvar lid) :: lvl, i+1)
    ) (now,#[],[],0)
  let type := cinfo.type.instantiateLevelParams cinfo.levelParams us.reverse
  modifyMCtx (fun _ => mctx)
  return (cache,num,type)


def parseEqIff (goal : Expr) : Option (Bool × Expr × Expr) :=
  let (h,as) := goal.getAppFnArgs
  if h == `Eq
  then
    .some (false, as[1]!, as[2]!)
  else
    if h == `Iff
    then
      .some (true, as[0]!, as[1]!)
    else
      .none


/-- Bool in output is true if its an rw-thm which has a sink not in the goal-/
partial def processForMain (l1 : LocalContext) (l2 : LocalInstances)
  (module : Name) (thmIdx : Nat)
  (thmName : Name ⊕ FVarId) (lvlC : Array (LMVarId × Nat)) (lvlN : Nat) (T : Expr)
  : MetaM (Bool × List ThmFormat) :=
  do
  let rec go (l1 : LocalContext) (l2 : LocalInstances)
    (hyps : Array HypType) (decls : Array (MVarId × MetavarDecl)) (userNames : Array (Name × MVarId))
    (type : Expr) (pos : Nat) (sinkCand : List (Nat × Nat))
    : MetaM (Bool × List ThmFormat) := do
    match type with
    | .letE _ _ V B _ => do
        go l1 l2 hyps decls userNames (Expr.instantiate1 B V) pos sinkCand
    | .forallE _ T nx bi => do
        let lid := lnode module thmIdx pos
        let T := T.cleanupAnnotations
        let mv ← mkMvarStdNoCoE lid T
        let dec ← mv.mvarId!.getDecl
        let hyps :=
          match bi with
          | .instImplicit => hyps.push <| .inst T
          | _ => hyps.push <| .reg T
        let decls := decls.push (⟨lid⟩,dec)
        let userNames := userNames.push (lid,⟨lid⟩)
        let nx := Expr.instantiate1 nx mv
        let affected := T.getLnodePos
        let sinkCand :=
          match bi with
          | .instImplicit => sinkCand -- instances won't be sinks nor affect sinks
          | _ => (pos, affected.length) :: (sinkCand.filter (fun (x,_) => !(affected.contains x)))
        go l1 l2 hyps decls userNames nx (pos + 1) sinkCand
    | goal =>
        let sinkCand := sinkCand.mergeSort (fun x y => x.2 ≥ y.2)
        -- *note* we sort the sinks by decreasing number of dependencies
        match parseEqIff goal with
        | .none =>
            let pred? ← IsProp goal l1 l2
            let res : ThmFormat :=
              .std thmName lvlN pred? hyps ⟨lvlC, decls, userNames⟩ hyps.size goal (sinkCand.map Prod.fst)
            return (false, [res])
        | .some (iff?, left, right) =>
            let goalDeps := goal.getLnodePos
            let sinkCand := (sinkCand.map Prod.fst)
            let sinksNotInGoal? := sinkCand.any (fun x => !(goalDeps.contains x))
            let resN : ThmFormat :=
              .rw thmName lvlN (if iff? then .iff_mp else .eq_mp)
                  left right hyps ⟨lvlC, decls, userNames⟩ hyps.size sinkCand
            let resS : ThmFormat :=
              .rw thmName lvlN (if iff? then .iff_mpr else .eq_mpr)
                  right left hyps ⟨lvlC, decls, userNames⟩ hyps.size sinkCand
            return (sinksNotInGoal?, [resN,resS])
  go l1 l2 #[] #[] #[] T 0 []


partial def processForCache
  (module : Name) (thmIdx : Nat) (cinfo : ConstantInfo)
  : MetaM (Bool × List ThmFormat) :=
  do
  let (lvlC,lvlN,T) ← levelsForCache module thmIdx cinfo
  processForMain {} {} module thmIdx (.inl cinfo.name) lvlC lvlN T


partial def processForQuery (l1 : LocalContext) (l2 : LocalInstances)
  (gnodeIdx : Nat) (type : Expr) : MetaM (Bool × List ThmFormat) :=
  do
  processForMain l1 l2 `processForQuery gnodeIdx (.inr <| ⟨gnode gnodeIdx⟩) #[] 0 type
