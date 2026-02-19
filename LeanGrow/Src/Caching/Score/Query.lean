/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Caching.Score.Generalize
import LeanGrow.Src.SampleGenScore.Gen.GenQueryBack
import LeanGrow.Src.SampleGenScore.Gen.GenQueryForw



open Lean Meta System



unsafe def query_thm_core
  {IdxCollType : Type} [Repr IdxCollType] [ToString IdxCollType] [Inhabited IdxCollType]
  (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β)
  (intersect difference union : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (empty : IdxCollType) (subsetOf : IdxCollType → IdxCollType → Bool)
  (mod : Name) (back? : Bool)
  (goal : Expr) (ltx : PaIn IdxCollType) (thmName : Name)
  : MetaM Unit := do
  let cachePath ← findLeanGrowCacheDir
  let loadpath := FilePath.join cachePath ((FilePath.toString (LeanGrow.genOfModuleName_thmKey mod)))
  let (sams,reg) ← unpickle (scoreThmKey IdxCollType) loadpath
  for j in Array.range sams.levelNum do
    let ln :=  .num sams.sampleName j
    let _ ← mkLevelMVarOfName ln
  let mut i := 0
  for T in sams.types do
    let ln := .num sams.sampleName i
    let _ ← mkMvarWiU ln (.num (.str .anonymous "?m") i) T
    i := i+1
  let l1 := (← getLCtx)
  let l2 := (← getLocalInstances)
  IO.println "Done loading!"
  IO.println "Score from goal:"
  let .some scores := (if back? then sams.regularBack else sams.regularForw).find? thmName.toString.toUTF8 | IO.println s!"No key {thmName} in cache"
  let is := scores.goalPain.getIndices empty union
  let .mk res l1 l2 ← PaIn.genQueryBackNoLoadMain
    empty? intersect union empty
    l1 l2 is 2 goal scores.goalPain
  IO.println s!"Matching inds : {repr res}"
  let w := fold res 0 (fun i r => scores.goalWeights[i]! + r)
  IO.println s!"Weight {repr w} vs total weight {scores.goalTotal}, ie. ratio {repr (w.toFloat / scores.goalTotal.toFloat)}"
  IO.println "Score from hyps:"
  let .mk _ ex _ ← PaIn.genQueryForwNoLoadMain
    intersect difference union empty? empty subsetOf
    l1 l2 ltx scores.hypSetTrie
  IO.println s!"Exact matches inds : {repr ex}"
  let w := ex.foldl (fun r (_,s) => s + r) 0
  IO.println s!"Weight {repr w} vs total weight {scores.hypTotal}, ie. ratio {repr (w.toFloat / scores.hypTotal.toFloat)}"



#check 1

-- #exit

unsafe def query_thm_main
  (mod : Name) (back? : Bool)
  (goal : Expr) (ltx : PaIn UInt32Array)  (thmName : Name)
  : MetaM Unit := do
  query_thm_core
    (fun is i f => is.foldl i (fun i s => f i.toNat s))
    UInt32Array.inter UInt32Array.diff UInt32Array.union
    UInt32Array.isEmpty UInt32Array.empty UInt32Array.subsetOf
    mod back? goal ltx thmName


#check 1


unsafe def query_gh_core
  {IdxCollType : Type} [Repr IdxCollType] [ToString IdxCollType] [Inhabited IdxCollType]
  (foldM : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → MetaM β) → MetaM β)
  (intersect difference union : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (empty : IdxCollType) (subsetOf : IdxCollType → IdxCollType → Bool)
  (mod : Name) (back? : Bool)
  (goal : Expr) (ltx : PaIn IdxCollType)
  : MetaM Unit := do
  let cachePath ← findLeanGrowCacheDir
  let loadpath := FilePath.join cachePath ((FilePath.toString (LeanGrow.genOfModuleName_ghKey mod)))
  let (sams,reg) ← unpickle (scoreGHKey IdxCollType) loadpath
  for j in Array.range sams.levelNum do
    let ln :=  .num sams.sampleName j
    let _ ← mkLevelMVarOfName ln
  let mut i := 0
  for T in sams.types do
    let ln := .num sams.sampleName i
    let _ ← mkMvarWiU ln (.num (.str .anonymous "?m") i) T
    i := i+1
  let l1 := (← getLCtx)
  let l2 := (← getLocalInstances)
  IO.println "Done loading!"
  let data := if back? then sams.regularBack else sams.regularForw
  let is := data.goalPain.getIndices empty union
  let .mk res l1 l2 ← PaIn.genQueryBackNoLoadMain
    empty? intersect union empty
    l1 l2 is 2 goal data.goalPain
  IO.println s!"Matching inds : {repr res}"
  foldM res () (fun i _ => do
    let gw := data.goalWeights[i]!
    IO.println s!"Goal weight {repr gw} vs total weight {data.goalTotal}, ie. ratio {repr (gw.toFloat / data.goalTotal.toFloat)}"
    let H := data.hypEntries[i]!
    let .mk _ ex _ ← PaIn.genQueryForwNoLoadMain
      intersect difference union empty? empty subsetOf
      l1 l2 ltx H.hypSetTrie
    ex.foldlM (fun _ ct =>
      ct.foldM () (fun n i _ => do
        IO.println s!"Theorem {String.fromUTF8! n}"
        let hw := H.hypWeights[i]!
        IO.println s!"Hyp weight {repr hw} vs total weight {H.hypTotal}, ie. ratio {repr (hw.toFloat / H.hypTotal.toFloat)}"
        )
      ) ()
    )


#check 1



unsafe def query_gh_main
  (mod : Name) (back? : Bool)
  (goal : Expr) (ltx : PaIn UInt32Array)
  : MetaM Unit := do
  query_gh_core
    (fun is i f => is.foldlM i (fun i s => f i.toNat s))
    UInt32Array.inter UInt32Array.diff UInt32Array.union
    UInt32Array.isEmpty UInt32Array.empty UInt32Array.subsetOf
    mod back? goal ltx


#check 1


-- TODO : subpatterns, conjecturables
