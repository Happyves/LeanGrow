
/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.SampleGenScore.Gen.Subpattern
import LeanGrow.Src.SampleGenScore.Sample

open Lean Meta



@[specialize]
def test_subSample_cvbThm
  (thmNames : Array Name)
  (depthDig depthStart depthStop : Nat) (deltaFuzz zetaFuzz : Option Nat)
  {IdxCollType : Type} [Repr IdxCollType]
  (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β) (empty : IdxCollType)
  (singleton : Nat → IdxCollType) (insert : Nat → IdxCollType → IdxCollType)
  (insertMulti intersect union difference : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (size : IdxCollType → Nat) (contains : Nat → IdxCollType → Bool)
  (genCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (commonType : Expr) → (branchDepth : Nat) → Bool)
  (freqCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (branchDepth : Nat) → Bool)
  (onlyInd : Bool)
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
  samples := (if onlyInd then samples.foldl .nil (fun w x y z L => match w with | .induc .. => ListProd4.cons w x y z L | _ => L) else samples)
  mtrace on .zero with s!" done sampling"
  let sorted : CTrie (Nat × PaIn IdxCollType) := .empty
  let .mk sorted types l1 l2 ← samples.foldlM (Prod4.mk sorted (#[] : Array Expr) L1 L2)
    (fun sd _ goal _ B@(.mk sorted types l1 l2) => do
      match sd with
      | .thm n =>
          let .mk types sorted ← cvb_thms_sampleClassify_subPat
            empty singleton insert l1 l2 n goal sampleName types sorted
          return .mk sorted types l1 l2
      | _ =>
          return B
      )
  mtrace on .zero with s!" done classifying"
  let .mk (_,types) res ← cvb_thms_genMain_subPat
    fold empty insert insertMulti intersect union difference
    empty? size contains l1 l2 genCondition freqCondition sampleName
    types #[] sorted
  mtrace on .zero with s!" done generalising"
  withLCtx l1 l2 <| do
    let mut i := 0
    IO.println "Types:"
    for T in types do
      IO.println s!"{i} : {← ppExpr T}"
      i := i+1
    res.foldM () (fun n v _ => do
      IO.println s!"\nTheorem: {String.fromUTF8! n}"
      IO.println s!"Subpatterns: {← v.1.pp l1 l2 [] 0 intersect empty?}"
      IO.println s!"Weights {v.2.mapIdx Prod.mk}"
      )

#check 1

@[specialize]
def test_subSample_cvbGoalHyp
  (thmNames : Array Name)
  (depthDig depthStart depthStop : Nat) (deltaFuzz zetaFuzz : Option Nat)
  {IdxCollType : Type} [Repr IdxCollType]
  (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β) (empty : IdxCollType)
  (singleton : Nat → IdxCollType) (insert : Nat → IdxCollType → IdxCollType)
  (insertMulti intersect union difference : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (size : IdxCollType → Nat) (contains : Nat → IdxCollType → Bool)
  (genCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (commonType : Expr) → (branchDepth : Nat) → Bool)
  (freqCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (branchDepth : Nat) → Bool)
  (onlyInd : Bool)
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
  samples := (if onlyInd then samples.foldl .nil (fun w x y z L => match w with | .induc .. => ListProd4.cons w x y z L | _ => L) else samples)
  mtrace on .zero with s!" done sampling"
  let state : Prod3 Nat (PaIn IdxCollType) (Array ByteArray) := .mk 0 .dead #[]
  let .mk sorted types l1 l2 ← samples.foldlM (Prod4.mk state (#[] : ) L1 L2)
    (fun sd _ goal _ B@(.mk state types l1 l2) => do
      match sd with
      | .thm n =>
          let sorted ← cvb_goal_hyp_sampleClassify_subPat
            empty singleton insert
            l1 l2 n goal sampleName types state
          return .mk (.mk sorted.2 sorted.3 sorted.4) sorted.1 l1 l2
      | _ =>
          return B
      )
  mtrace on .zero with s!" done classifying"
  let .mk sT W _ _ types ← cvb_goal_hyp_genMain_subPat
    fold empty insert insertMulti intersect union difference
    empty? size contains l1 l2 genCondition freqCondition sampleName
    types #[] sorted
  mtrace on .zero with s!" done generalising"
  withLCtx l1 l2 <| do
    let mut i := 0
    IO.println "Types:"
    for T in types do
      IO.println s!"{i} : {← ppExpr T}"
      i := i+1
    IO.println s!"\nGoals: {← sT.pp l1 l2 [] 0 intersect empty?}"
    IO.println s!"Goal weights {W.mapIdx (fun i x => (i, x.toList))}"


#check 1


#check UInt32Array


def test_subSample_cvbThm_S
  (thmNames : Array Name)
  (depthDig depthStart depthStop : Nat) (deltaFuzz zetaFuzz : Option Nat)
  (genCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (commonType : Expr) → (branchDepth : Nat) → Bool)
  (freqCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (branchDepth : Nat) → Bool)
  (onlyInd : Bool)
  : MetaM Unit :=
  @test_subSample_cvbThm
    thmNames depthDig depthStart depthStop deltaFuzz zetaFuzz
    UInt32Array _ (fun is i f => is.foldl i (fun i s => f i.toNat s)) UInt32Array.empty
    (fun n => UInt32Array.single n.toUInt32) (fun x y => y.oInsert x.toUInt32)
    UInt32Array.union UInt32Array.inter UInt32Array.union UInt32Array.diff UInt32Array.isEmpty
    UInt32Array.size (fun x y => y.oContains x.toUInt32)
    genCondition freqCondition onlyInd


#check 1

def test_subSample_cvbGoalHyp_S
  (thmNames : Array Name)
  (depthDig depthStart depthStop : Nat) (deltaFuzz zetaFuzz : Option Nat)
  (genCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (commonType : Expr) → (branchDepth : Nat) → Bool)
  (freqCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (branchDepth : Nat) → Bool)
  (onlyInd : Bool)
  : MetaM Unit :=
  @test_subSample_cvbGoalHyp
    thmNames depthDig depthStart depthStop deltaFuzz zetaFuzz
    UInt32Array _ (fun is i f => is.foldl i (fun i s => f i.toNat s)) UInt32Array.empty
    (fun n => UInt32Array.single n.toUInt32) (fun x y => y.oInsert x.toUInt32)
    UInt32Array.union UInt32Array.inter UInt32Array.union UInt32Array.diff UInt32Array.isEmpty
    UInt32Array.size (fun x y => y.oContains x.toUInt32)
    genCondition freqCondition onlyInd

#check 1
