
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
  mtracing
  let sampleName := `testSam
  let env ← getEnv
  let preS ← mkPreProCongr
  let mut L1 := ← getLCtx
  let mut L2 := ← getLocalInstances
  let mut samples : ListProd4 SampleData (List FVarId) Expr (List Expr) := .nil
  for thmName in thmNames do
    let .some (.thmInfo I) := env.find? thmName | throwError "Bad name"
    let .mk p fvs l1 l2 ← LambdaLetTelescope I.value 0 L1 L2
    let .mk res _ l1 l2 ← sampleCoreBack preS .empty l1 l2 depthDig depthStart depthStop deltaFuzz zetaFuzz (.cons (.raw p) (fvs.map Expr.fvarId!).toList .nil) samples .nil
    samples := res
    L1 := l1
    L2 := l2
  mtrace on .zero with s!" done sampling"
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
            empty singleton insert intersect empty? l1 l2 n goal hyps sorted
          return .mk sorted types l1 l2
      | _ =>
          return B
      )
  mtrace on .zero with s!" done classifying"
  let .mk (_,cleanTypes) res ← cvb_thms_genMain
    fold empty insert insertMulti intersect union difference
    empty? size contains l1 l2 genCondition freqCondition sampleName
    types #[] sorted
  mtrace on .zero with s!" generalised"
  withLCtx l1 l2 <| do
    let mut i := 0
    IO.println "Types:"
    for T in cleanTypes do
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
  mtracing
  let sampleName := `testSam
  let env ← getEnv
  let preS ← mkPreProCongr
  let mut L1 := ← getLCtx
  let mut L2 := ← getLocalInstances
  let mut samples : ListProd4 SampleData (List FVarId) Expr (List Expr) := .nil
  for thmName in thmNames do
    let .some (.thmInfo I) := env.find? thmName | throwError "Bad name"
    let .mk p fvs l1 l2 ← LambdaLetTelescope I.value 0 L1 L2
    let .mk res _ l1 l2 ← sampleCoreBack preS .empty l1 l2 depthDig depthStart depthStop deltaFuzz zetaFuzz (.cons (.raw p) (fvs.map Expr.fvarId!).toList .nil) samples .nil
    samples := res
    L1 := l1
    L2 := l2
  mtrace on .zero with s!" done sampling"
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
  mtrace on .zero with s!" done classifying"
  mtrace on .one with s!" types {← types.mapIdxM (fun i x => return (i, ← ppExpr x))}"
  let .mk _ cleanedTypes res ← cvb_goal_hyp_genMain
    fold empty shiftAdd insert insertMulti intersect union difference
    empty? size contains l1 l2 genCondition freqCondition sampleName
    types #[] sorted
  mtrace on .zero with s!" done generalising"
  withLCtx l1 l2 <| do
    let mut i := 0
    IO.println "Types:"
    for T in cleanedTypes do
      IO.println s!"{i} : {← ppExpr T}"
      i := i+1
    IO.println s!"\nGoals: {← res.goalPain.pp l1 l2 [] 0 intersect empty?}"
    IO.println s!"Goal weights {res.goalWeights.mapIdx Prod.mk}"
    i := 0
    for entry in res.hypEntries do
      IO.println s!"\nIdx {i}\nHyps: {← entry.hypSetTrie.pp 0 (fun p => p.pp l1 l2 [] 0 intersect empty?) (fun t => return s!"{t.toList}")}"
      IO.println s!"Hyp weights {entry.hypWeights.mapIdx Prod.mk}"
      i := i+1

#check 1


#check UInt32Array


def test_backSample_cvbThm_S
  (thmNames : Array Name)
  (depthDig depthStart depthStop : Nat) (deltaFuzz zetaFuzz : Option Nat)
  (genCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (commonType : Expr) → (branchDepth : Nat) → Bool)
  (freqCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (branchDepth : Nat) → Bool)
  : MetaM Unit :=
  @test_backSample_cvbThm
    thmNames depthDig depthStart depthStop deltaFuzz zetaFuzz
    UInt32Array _ (fun is i f => is.foldl i (fun i s => f i.toNat s)) UInt32Array.empty
    (fun n => UInt32Array.single n.toUInt32) (fun x y => y.oInsert x.toUInt32)
    UInt32Array.union UInt32Array.inter UInt32Array.union UInt32Array.diff UInt32Array.isEmpty
    UInt32Array.size (fun x y => y.oContains x.toUInt32)
    genCondition freqCondition


#check 1
#check UInt32Array.shiftAdd



def test_backSample_cvbGoalHyp_S
  (thmNames : Array Name)
  (depthDig depthStart depthStop : Nat) (deltaFuzz zetaFuzz : Option Nat)
  (genCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (commonType : Expr) → (branchDepth : Nat) → Bool)
  (freqCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (branchDepth : Nat) → Bool)
  : MetaM Unit :=
  @test_backSample_cvbGoalHyp
    thmNames depthDig depthStart depthStop deltaFuzz zetaFuzz
    UInt32Array _ (fun is i f => is.foldl i (fun i s => f i.toNat s)) UInt32Array.empty
    (fun n => UInt32Array.single n.toUInt32) (fun x y => y.oInsert x.toUInt32)
    UInt32Array.union UInt32Array.inter UInt32Array.union UInt32Array.diff UInt32Array.isEmpty
    UInt32Array.size (fun x y => y.oContains x.toUInt32) (fun is => if is.isEmpty then panic! "[test_backSample_cvbGoalHyp_S] head" else is[0]!.toNat)
    (fun x y => x.shiftAdd y.toUInt32)
    genCondition freqCondition

#check 1
