
/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.SampleGenScore.Gen.Conveyorbelts
import LeanGrow.Src.SampleGenScore.Sample

open Lean Meta


@[specialize]
def test_backSample_cvbThm
  (thmNames : Array Name)
  (depthDig depthStart depthStop : Nat) (deltaFuzz zetaFuzz : Option Nat)
  {IdxCollType : Type} [Repr IdxCollType]
  (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β) (empty : IdxCollType)
  (singleton : Nat → IdxCollType) (insert : Nat → IdxCollType → IdxCollType)
  (insertMulti intersect union difference : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (size : IdxCollType → Nat) (contains : Nat → IdxCollType → Bool)
  (genCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (commonType : Expr) → (branchDepth : Nat) → Bool)
  (freqCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (branchDepth : Nat) → Bool)
  : MetaM Unit := do
  let sampleName := `testSam
  let env ← getEnv
  let preS ← mkPreProCongr
  let mut L1 := ← getLCtx
  let mut L2 := ← getLocalInstances
  let mut samples : ListProd4 SampleData (List FVarId) Expr (List Expr) := .nil
  for thmName in thmNames do
    let .some (.thmInfo I) := env.find? thmName | throwError "Bad name"
    let .mk p fvs l1 l2 ← LambdaLetTelescopeWW I.value 0 L1 L2
    let .mk res l1 l2 ← sampleCoreBack preS l1 l2 depthDig depthStart depthStop deltaFuzz zetaFuzz (.cons (.raw p) (fvs.map Expr.fvarId!).toList .nil) samples
    samples := res
    L1 := l1
    L2 := l2
  let sorted : CTrie (Prod5 Nat Nat (ListProd Nat (List Nat)) (PaIn IdxCollType) (PaIn IdxCollType)) := .empty
  let .mk sorted types l1 l2 ← samples.foldlM (Prod4.mk sorted (#[] : Array Expr) L1 L2)
    (fun sd _ goal hyps B@(.mk sorted types l1 l2) => do
      match sd with
      | .thm n =>
          let .mk goal (types, dict) l1 l2 ← goal.translateToLnodes l1 l2 sampleName types {}
          let .mk hyps (types, _) l1 l2 ← hyps.foldlM (fun (.mk L (types, dict) l1 l2) h => do
            let .mk h (types, dict) l1 l2 ← h.translateToLnodes l1 l2 sampleName types dict
            return .mk (h :: L) (types, dict) l1 l2
            ) (Prod4.mk [] (types, dict) l1 l2)
          let sorted ← cvb_thms_sampleClassify
            empty singleton insert l1 l2 n goal hyps sorted
          return .mk sorted types l1 l2
      | _ =>
          return B
      )
  let .mk types res ← cvb_thms_genMain
    fold empty insert insertMulti intersect union difference
    empty? size contains l1 l2 genCondition freqCondition sampleName
    types sorted
  withLCtx l1 l2 <| do
    let mut i := 0
    IO.println "Types:"
    for T in types do
      IO.println s!"{i} : {← ppExpr T}"
      i := i+1
    res.foldM () (fun n v _ => do
      IO.println s!"\nTheorem: {String.fromUTF8! n}"
      IO.println s!"Goals: {← v.goalPain.pp l1 l2 [] 0 intersect empty?}"
      IO.println s!"Goal weights {v.goalWeights.mapIdx Prod.mk}"
      IO.println s!"Hyps: {← v.hypSetTrie.pp 0 (fun p => p.pp l1 l2 [] 0 intersect empty?) (fun (x,y) => return s!"Idx {x}, weight {y}")}"
      )

#check 1

@[specialize]
def test_backSample_cvbGoalHyp
  (thmNames : Array Name)
  (depthDig depthStart depthStop : Nat) (deltaFuzz zetaFuzz : Option Nat)
  {IdxCollType : Type} [Repr IdxCollType]
  (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β) (empty : IdxCollType)
  (singleton : Nat → IdxCollType) (insert : Nat → IdxCollType → IdxCollType)
  (insertMulti intersect union difference : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (size : IdxCollType → Nat) (contains : Nat → IdxCollType → Bool) (head : IdxCollType → Nat)
  (shiftAdd : IdxCollType → Nat → IdxCollType)
  (genCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (commonType : Expr) → (branchDepth : Nat) → Bool)
  (freqCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (branchDepth : Nat) → Bool)
  : MetaM Unit := do
  let sampleName := `testSam
  let env ← getEnv
  let preS ← mkPreProCongr
  let mut L1 := ← getLCtx
  let mut L2 := ← getLocalInstances
  let mut samples : ListProd4 SampleData (List FVarId) Expr (List Expr) := .nil
  for thmName in thmNames do
    let .some (.thmInfo I) := env.find? thmName | throwError "Bad name"
    let .mk p fvs l1 l2 ← LambdaLetTelescopeWW I.value 0 L1 L2
    let .mk res l1 l2 ← sampleCoreBack preS l1 l2 depthDig depthStart depthStop deltaFuzz zetaFuzz (.cons (.raw p) (fvs.map Expr.fvarId!).toList .nil) samples
    samples := res
    L1 := l1
    L2 := l2
  let state : Prod3 Nat (PaIn IdxCollType) (Array (Prod4 Nat Nat (ListProd ByteArray (List Nat)) (PaIn IdxCollType))) := .mk 0 .dead #[]
  let .mk sorted types l1 l2 ← samples.foldlM (Prod4.mk state (#[] : Array Expr) L1 L2)
    (fun sd _ goal hyps B@(.mk state types l1 l2) => do
      match sd with
      | .thm n =>
          let .mk goal (types, dict) l1 l2 ← goal.translateToLnodes l1 l2 sampleName types {}
          let .mk hyps (types, _) l1 l2 ← hyps.foldlM (fun (.mk L (types, dict) l1 l2) h => do
            let .mk h (types, dict) l1 l2 ← h.translateToLnodes l1 l2 sampleName types dict
            return .mk (h :: L) (types, dict) l1 l2
            ) (Prod4.mk [] (types, dict) l1 l2)
          let sorted ← cvb_goal_hyp_sampleClassify
            empty singleton insert empty? intersect union head
            l1 l2 n goal hyps state
          return .mk sorted types l1 l2
      | _ =>
          return B
      )
  let .mk types res ← cvb_goal_hyp_genMain
    fold empty shiftAdd insert insertMulti intersect union difference
    empty? size contains l1 l2 genCondition freqCondition sampleName
    types sorted
  withLCtx l1 l2 <| do
    let mut i := 0
    IO.println "Types:"
    for T in types do
      IO.println s!"{i} : {← ppExpr T}"
      i := i+1
    IO.println s!"\nGoals: {← res.goalPain.pp l1 l2 [] 0 intersect empty?}"
    IO.println s!"Goal weights {res.goalWeights.mapIdx Prod.mk}"
    i := 0
    for entry in res.hypEntries do
      IO.println s!"Hyps: {← entry.hypSetTrie.pp 0 (fun p => p.pp l1 l2 [] 0 intersect empty?) (fun t => return s!"{t.toList}")}"
      IO.println s!"Hyp weights {entry.hypWeights.mapIdx Prod.mk}"
      i := i+1

#check 1


#check_failure UInt32Array

#exit

def test_backSample_cvbThm_S
  (thmNames : Array Name)
  (depthDig depthStart depthStop : Nat) (deltaFuzz zetaFuzz : Option Nat)
  {IdxCollType : Type} [Repr IdxCollType]
  (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β) (empty : IdxCollType)
  (singleton : Nat → IdxCollType) (insert : Nat → IdxCollType → IdxCollType)
  (insertMulti intersect union difference : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (size : IdxCollType → Nat) (contains : Nat → IdxCollType → Bool)
  (genCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (commonType : Expr) → (branchDepth : Nat) → Bool)
  (freqCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (branchDepth : Nat) → Bool)
  : MetaM Unit :=
  test_backSample_cvbThm
    thmNames depthDig depthStart depthStop deltaFuzz zetaFuzz

#check 1
