
/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.SampleGenScore.Gen.Conveyorbelts
import LeanGrow.Src.SampleGenScore.Gen.GenQueryBack
import LeanGrow.Src.SampleGenScore.Gen.GenQueryForw



open Lean Meta

variable {IdxCollType : Type _}



partial def Lean.Expr.getSubPat
  (l1 : LocalContext) (l2 : LocalInstances)
  (init : List Expr) (e : Expr) : MetaM (Prod3 (List Expr) LocalContext LocalInstances) := do
    match e with
    | .mdata _ e => e.getSubPat l1 l2 init
    | .letE _ _ V B _ => (Expr.instantiate1 B V).getSubPat l1 l2 init
    | .lam n T B _ | .forallE n T B _ =>
      let .mk fv l1 l2 ← WithLocalDeclU n T l1 l2
      let B := Expr.instantiate1 B (.fvar fv)
      if (← IsProp T l1 l2) && (← IsClass? T l1 l2).isSome
      then
        B.getSubPat l1 l2 (T :: init)
      else
        B.getSubPat l1 l2 init
    | .proj .. =>
      return .mk (e :: init) l1 l2
    | .app .. =>
      let h := e.getAppFn'
      let as := e.getAppArgs
      let finfo ← withLCtx l1 l2 <| getFunInfo h
      let init := if h.isAtomic then init else h :: init
      let .mk _ pats l1 l2 ← finfo.paramInfo.foldlM (fun (.mk i R l1 l2) info => do
        match info.binderInfo with
        | .default =>
          if info.hasFwdDeps
          then return .mk (i+1) R l1 l2
          else
            let a := as[i]!
            match a with
            | .letE .. | .lam .. | .forallE .. | .app .. | .mdata .. | .proj .. =>
              let .mk R l1 l2 ← a.getSubPat l1 l2 R
              return .mk (i+1) R l1 l2
            | _ =>
              -- let R := if a.isAtomic then R else a :: R
              return .mk (i+1) R l1 l2
        | _ => return .mk (i+1) R l1 l2
        ) (Prod4.mk 0 init l1 l2)
      return .mk (e :: pats) l1 l2
    | _ =>
      return .mk init l1 l2


#check 1

/-- Difference: expects goal and hyps *without* translation to lnodes -/
@[specialize, inline]
partial def cvb_thms_sampleClassify_subPat
  [Repr IdxCollType]
  (emptyCol : IdxCollType) (singleton : Nat → IdxCollType) (insert : Nat → IdxCollType → IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (sampleThm : Name) (sampleGoal : Expr)
  (sampleName : Name) (types : Array Expr)
  (sorted : CTrie (Prod Nat (PaIn IdxCollType)))
  : MetaM (Array Expr × CTrie (Prod Nat (PaIn IdxCollType))) := do
    let .mk gsubP l1 l2 ← sampleGoal.getSubPat l1 l2 []
    let .mk gsubP (types,_) l1 l2 ← gsubP.foldlM (fun (.mk l (types,dict) l1 l2) e => do
      let .mk r (types,dict) l1 l2 ← e.translateToLnodes l1 l2 sampleName types dict
      return .mk (r :: l) (types,dict) l1 l2
      ) (Prod4.mk [] (types,{}) l1 l2)
    let sampleThm := sampleThm.toString.toUTF8
    let tr ← sorted.upsertM sampleThm (fun
      | .none => do
          let .mk ngi ngT ← gsubP.foldlM (fun (.mk nhi nT) e => do
            let .mk iT _ _ ← nT.insert l1 l2 e nhi emptyCol singleton insert
            return .mk (nhi + 1)  iT
            ) (.mk 0 PaIn.dead : Prod ..)
          return .some <| .mk ngi ngT
      | .some (Prod.mk initSamIdx igT) => do
          let .mk ngi ngT ← gsubP.foldlM (fun (.mk nhi nT) e => do
            let .mk iT _ _ ← nT.insert l1 l2 e nhi emptyCol singleton insert
            return .mk (nhi + 1)  iT
            ) (.mk initSamIdx igT : Prod ..)
          return .some <| .mk ngi ngT
      )
    return (types, tr)


#check 1


/-- Difference: expects goal and hyps *without* translation to lnodes -/
@[specialize, inline]
partial def cvb_goal_hyp_sampleClassify_subPat
  [Repr IdxCollType]
  (emptyCol : IdxCollType) (singleton : Nat → IdxCollType) (insert : Nat → IdxCollType → IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (sampleThm : Name) (sampleGoal : Expr)
  (sampleName : Name) (types : Array Expr)
  (state : Prod3 Nat (PaIn IdxCollType) (Array ByteArray))
  : MetaM (Prod4 (Array Expr) Nat (PaIn IdxCollType) (Array ByteArray)) := do
    let .mk gsubP l1 l2 ← sampleGoal.getSubPat l1 l2 []
    let gsubPN := gsubP.length
    let .mk gsubP (types,_) l1 l2 ← gsubP.foldlM (fun (.mk l (types,dict) l1 l2) e => do
      let .mk r (types,dict) l1 l2 ← e.translateToLnodes l1 l2 sampleName types dict
      return .mk (r :: l) (types,dict) l1 l2
      ) (Prod4.mk [] (types,{}) l1 l2)
    let .mk initSamIdx goalPain sorted := state
    let sampleThm := sampleThm.toString.toUTF8
    let .mk ngi ngT ← gsubP.foldlM (fun (.mk nhi nT) e => do
      let .mk iT _ _ ← nT.insert l1 l2 e nhi emptyCol singleton insert
      return .mk (nhi + 1)  iT
      ) (.mk initSamIdx goalPain : Prod ..)
    let sorted := sorted.pushN sampleThm gsubPN
    return .mk types ngi ngT sorted

#check 1


@[specialize, inline]
partial def cvb_thms_genMain_subPat [Repr IdxCollType]
  (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β) (empty : IdxCollType)
  (insert : Nat → IdxCollType → IdxCollType)
  (insertMulti intersect union difference : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (size : IdxCollType → Nat) (contains : Nat → IdxCollType → Bool)
  (l1 : LocalContext) (l2 : LocalInstances)
  (genCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (commonType : Expr) → (branchDepth : Nat) → Bool)
  (freqCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (branchDepth : Nat) → Bool)
  (sampleName : Name) (allTypes cleanTypes : Array Expr)
  (sorted : CTrie (Prod Nat (PaIn IdxCollType)))
  : MetaM (Prod ((Array Expr) × (Array Expr)) (CTrie (Prod3 (PaIn IdxCollType) (Array Nat) Nat))) := do
    sorted.foldMapM (allTypes, cleanTypes) (fun entry (allTypes, cleanTypes) => do
      let .mk gT gW gw _ allTypes cleanTypes ← cvb_thms_genGoal
        fold empty insert insertMulti intersect union difference
        empty? size contains l1 l2 genCondition freqCondition
        entry.1 entry.2 sampleName allTypes cleanTypes
      return .mk (allTypes, cleanTypes) (.some (.mk gT gW gw))
      )

#check 1



@[specialize, inline]
partial def cvb_goal_hyp_genMain_subPat [Repr IdxCollType]
  (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β) (empty : IdxCollType)
  (insert : Nat → IdxCollType → IdxCollType)
  (insertMulti intersect union difference : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (size : IdxCollType → Nat) (contains : Nat → IdxCollType → Bool)
  (l1 : LocalContext) (l2 : LocalInstances)
  (genCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (commonType : Expr) → (branchDepth : Nat) → Bool)
  (freqCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (branchDepth : Nat) → Bool)
  (sampleName : Name) (allTypes cleanTypes : Array Expr)
  (state : Prod3 Nat (PaIn IdxCollType) (Array ByteArray))
  : MetaM (Prod5 (PaIn IdxCollType) (Array (CTrie Nat)) Nat (Array Expr) (Array Expr)) := do
  mtracing
  let .mk samIdx goalPain thms := state
  let weights := Array.replicate samIdx 1
  mtrace on .zero with s!" generalising"
  let .mk freqInd T allTypes _ _ ← generalizePaInCore
    fold empty insertMulti intersect union difference empty? l1 l2 genCondition freqCondition sampleName
    goalPain weights allTypes
  mtrace on .one with s!" generalised PaIn {← T.pp l1 l2 [] 0 intersect empty?}"
  mtrace on .zero with s!" found freqInd {repr freqInd}, deduplicating"
  let .mk T weights trans ← T.dedup insert union empty size contains fold weights freqInd
  mtrace on .zero with s!" deleting top mvars"
  let .mk T weights ntrans ← T.removeTopMvars insert union empty size contains fold weights
  let trans := translateMerge decl_name% trans ntrans
  mtrace on .zero with s!" running lnode garbadge collection on\nT : {← T.pp l1 l2 [] 0 intersect empty?}\nallTypes: {← allTypes.mapM ppExpr}\ncleanTypes: {← cleanTypes.mapM ppExpr}"
  let (T,cleanTypes,_) := lnodeGarbageCollection T allTypes cleanTypes
  mtrace on .zero with s!" done with lnode garbadge collection"
  let total := weights.foldl (fun x y => x+y) 0
  let mut next := Array.replicate weights.size CTrie.empty
  for (ini,new) in trans do
    let thm := thms[ini]!
    next := next.modify new (fun ct =>
      ct.upsert thm (fun
        | .none => .some weights[new]!
        | .some w => .some <| w + weights[new]!
        ))
  return Prod5.mk T next total allTypes cleanTypes

#check 1



namespace PaIn

@[specialize, inline]
partial def genQueryBackSubpatWiLoadMain
    [Repr IdxCollType] [ToString IdxCollType] [Inhabited IdxCollType]
    (empty? : IdxCollType → Bool) (intersect union : IdxCollType → IdxCollType → IdxCollType) (empty : IdxCollType)
    (l1 : LocalContext) (l2 : LocalInstances)
    (constr : IdxCollType)
    (revCountMax : Nat)
    (E : Expr) (T : PaIn IdxCollType)
    (sampleName : Name) (types : Array Expr)
    : MetaM (Prod3 IdxCollType LocalContext LocalInstances) :=
    do
    let _ ← mkLevelMVarOfName (.num sampleName 0)
    let mut i := 0
    for T in types do
      let _ ← mkMvarStdNoCoI (.num sampleName i) T
      i := i+1
    let .mk subp l1 l2 ← E.getSubPat l1 l2 []
    subp.foldlM (fun (.mk I l1 l2) E => do
      let .mk yes? _ inds l1 l2 ← genQueryBackCore empty? intersect union empty l1 l2 constr revCountMax E T
      if yes? == 3
      then
        return .mk (union I inds) l1 l2 -- deuplicate apperances of patterns will thus not be accounted for ...
      else
        return .mk empty l1 l2
      ) (Prod3.mk empty l1 l2)


@[specialize, inline]
partial def genQueryBackSubpatMain
    [Repr IdxCollType] [ToString IdxCollType] [Inhabited IdxCollType]
    (empty? : IdxCollType → Bool) (intersect union : IdxCollType → IdxCollType → IdxCollType) (empty : IdxCollType)
    (l1 : LocalContext) (l2 : LocalInstances)
    (constr : IdxCollType)
    (revCountMax : Nat)
    (E : Expr) (T : PaIn IdxCollType)
    : MetaM (Prod3 IdxCollType LocalContext LocalInstances) :=
    do
    let .mk subp l1 l2 ← E.getSubPat l1 l2 []
    subp.foldlM (fun (.mk I l1 l2) E => do
      let .mk yes? _ inds l1 l2 ← genQueryBackCore empty? intersect union empty l1 l2 constr revCountMax E T
      if yes? == 3
      then
        return .mk (union I inds) l1 l2 -- deuplicate appeaances of patterns will thus not be accounted for ...
      else
        return .mk empty l1 l2
      ) (Prod3.mk empty l1 l2)


end PaIn
