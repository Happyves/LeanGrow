
/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.SampleGenScore.Gen.ConjecturableBuild
import LeanGrow.Src.SampleGenScore.Sample

open Lean Meta

@[specialize]
def test_conjSample_cvbThm
  (thmNames : Array Name)
  (depthDig depthStart depthStop : Nat) (deltaFuzz zetaFuzz : Option Nat)
  {IdxCollType : Type} [Repr IdxCollType] [EmptyCollection IdxCollType]
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
    let .mk p fvs l1 l2 ← LambdaLetTelescope I.value 0 L1 L2
    let .mk res _ l1 l2 ← sampleCoreBack preS .empty l1 l2 depthDig depthStart depthStop deltaFuzz zetaFuzz (.cons (.raw p) (fvs.map Expr.fvarId!).toList .nil) samples .nil
    -- ↑ empty conj tree means only tactics will be recognized, noth thms
    samples := res
    L1 := l1
    L2 := l2
  samples := samples.foldl .nil (fun w x y z L => match w with | .thmC .. => ListProd4.cons w x y z L | _ => L)
  let state : Prod3 Nat (Array Expr) (CTrie (Prod6 Nat Nat (ListProd Nat (List Nat)) (PaIn IdxCollType) (PaIn IdxCollType) (Array (Nat × PaIn IdxCollType))))
    := .mk 0 #[] .empty
  let .mk _ types res ← samples.foldlM state
    (fun sd _ goal hyps st => do
      match sd with
      | .thmC n cjs =>
          cvb_thmConj_sampleClassify
            empty singleton insert L1 L2 n cjs goal hyps sampleName st
      | _ =>
          return st
      )
  let .mk types res ← cvb_thmConj_genMain
    fold empty insert insertMulti intersect union difference
    empty? size contains L1 L2 genCondition freqCondition sampleName
    types #[] res
  withLCtx L1 L2 <| do
    let mut i := 0
    IO.println "Pattern Types:"
    for T in types.2 do
      IO.println s!"{i} : {← ppExpr T}"
      i := i+1
    res.foldM () (fun n (.mk v _ pats) _ => do
      IO.println s!"\nTheorem: {String.fromUTF8! n}"
      IO.println s!"Goals: {← v.goalPain.pp L1 L2 [] 0 intersect empty?}"
      IO.println s!"Goal weights {v.goalWeights.mapIdx Prod.mk}"
      IO.println s!"Hyps: {← v.hypSetTrie.pp 0 (fun p => p.pp L1 L2 [] 0 intersect empty?) (fun (x,y) => return s!"Idx {x}, weight {y}")}"
      IO.println "\nPatterns:"
      let mut i := 0
      for p in pats do
        IO.println s!"\nIndex {i}"
        p.foldlM () (fun th w _ => do
          IO.println s!"Pat: {← ppExpr th.goal}\nHyps: {← th.hypsTypes.mapM ppExpr}\nWeight: {w}"
          )
        i := i+1
      )

#check 1
#print thmGenDataEntry


def test_conjSample_cvbThm_S
  (thmNames : Array Name)
  (depthDig depthStart depthStop : Nat) (deltaFuzz zetaFuzz : Option Nat)
  (genCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (commonType : Expr) → (branchDepth : Nat) → Bool)
  (freqCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (branchDepth : Nat) → Bool)
  : MetaM Unit :=
  @test_conjSample_cvbThm
    thmNames depthDig depthStart depthStop deltaFuzz zetaFuzz
    UInt32Array _ _ (fun is i f => is.foldl i (fun i s => f i.toNat s)) UInt32Array.empty
    (fun n => UInt32Array.single n.toUInt32) (fun x y => y.oInsert x.toUInt32)
    UInt32Array.union UInt32Array.inter UInt32Array.union UInt32Array.diff UInt32Array.isEmpty
    UInt32Array.size (fun x y => y.oContains x.toUInt32)
    genCondition freqCondition

#check 1
