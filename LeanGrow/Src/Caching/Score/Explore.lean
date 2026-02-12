/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Caching.Score.Generalize


open Lean Meta System


unsafe def explore_samClass_thm_core
  {IdxCollType : Type} [Repr IdxCollType]
  (intersect : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (mod : Name)
  : MetaM Unit := do
  let cachePath ← findLeanGrowCacheDir
  let loadpath := FilePath.join cachePath ((FilePath.toString (LeanGrow.sampleNameOfModuleName_thmKey mod)))
  let (sams,reg) ← unpickle (ProcessedSamplesThmKey IdxCollType) loadpath
  IO.println s!"Sample name : {sams.sampleName}"
  IO.println s!"\nLevelNum : {sams.levelNum}"
  IO.println "\nTypes:"
  let mut i := 0
  for T in sams.types do
    IO.println s!"{i} : {← ppExpr T}"
    i := i+1
  IO.println "\nRegular back:"
  sams.regularBack.foldM () (fun n v _ => do
      IO.println s!"\nTheorem: {String.fromUTF8! n}"
      IO.println s!"G idx {v.1} H idx {v.2} Dict {v.3}"
      IO.println s!"Gs: {← v.4.pp (← getLCtx) (← getLocalInstances) [] 0 intersect empty?}"
      IO.println s!"Hs: {← v.5.pp (← getLCtx) (← getLocalInstances) [] 0 intersect empty?}"
      )
  IO.println "\nRegular forward:"
  sams.regularForw.foldM () (fun n v _ => do
      IO.println s!"\nTheorem: {String.fromUTF8! n}"
      IO.println s!"G idx {v.1} H idx {v.2} Dict {v.3}"
      IO.println s!"Gs: {← v.4.pp (← getLCtx) (← getLocalInstances) [] 0 intersect empty?}"
      IO.println s!"Hs: {← v.5.pp (← getLCtx) (← getLocalInstances) [] 0 intersect empty?}"
      )
  IO.println "\nSubpats:"
  sams.subpat.foldM () (fun n v _ => do
      IO.println s!"\nTheorem: {String.fromUTF8! n}"
      IO.println s!"Idx {v.1}"
      IO.println s!"Pats: {← v.2.pp (← getLCtx) (← getLocalInstances) [] 0 intersect empty?}"
      )
  IO.println "\nConjecturable:"
  sams.conj.foldM () (fun n v _ => do
      IO.println s!"\nTheorem: {String.fromUTF8! n}"
      IO.println s!"G idx {v.1} H idx {v.2} Dict {v.3}"
      IO.println s!"Gs: {← v.4.pp (← getLCtx) (← getLocalInstances) [] 0 intersect empty?}"
      IO.println s!"Hs: {← v.5.pp (← getLCtx) (← getLocalInstances) [] 0 intersect empty?}"
      IO.println "\nPatterns:"
      let mut i := 0
      for p in v.6 do
        IO.println s!"\nIndex {i} total {p.1}\nGs: {← p.2.pp (← getLCtx) (← getLocalInstances) [] 0 intersect empty?}"
        i := i+1
      )
  -- not freeing the pickle

#check 1

unsafe def explore_samClass_thm_core_S
  (mod : Name)
  : MetaM Unit :=
    explore_samClass_thm_core
      UInt32Array.inter UInt32Array.isEmpty mod

#check 1


unsafe def explore_samClass_gh_core
  {IdxCollType : Type} [Repr IdxCollType]
  (intersect : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (mod : Name)
  : MetaM Unit := do
  let cachePath ← findLeanGrowCacheDir
  let loadpath := FilePath.join cachePath ((FilePath.toString (LeanGrow.sampleNameOfModuleName_thmKey mod)))
  let (sams,reg) ← unpickle (ProcessedSamplesGHKey IdxCollType) loadpath
  IO.println s!"Sample name : {sams.sampleName}"
  IO.println s!"\nLevelNum : {sams.levelNum}"
  IO.println "\nTypes:"
  let mut i := 0
  for T in sams.types do
    IO.println s!"{i} : {← ppExpr T}"
    i := i+1
  IO.println s!"\nRegular back:\nIdx: {sams.regularBack.1}\nPats: {← sams.regularBack.2.pp (← getLCtx) (← getLocalInstances) [] 0 intersect empty?}"
  i := 0
  for v in sams.regularBack.3 do
    IO.println s!"Idx : {i} G idx {v.1} H idx {v.2} Dict {v.3}"
    IO.println s!"Hs: {← v.4.pp (← getLCtx) (← getLocalInstances) [] 0 intersect empty?}"
    i := i+1
  IO.println s!"\nRegular forw:\nIdx: {sams.regularForw.1}\nPats: {← sams.regularForw.2.pp (← getLCtx) (← getLocalInstances) [] 0 intersect empty?}"
  i := 0
  for v in sams.regularForw.3 do
    IO.println s!"Idx : {i} G idx {v.1} H idx {v.2} Dict {v.3}"
    IO.println s!"Hs: {← v.4.pp (← getLCtx) (← getLocalInstances) [] 0 intersect empty?}"
    i := i+1
  IO.println s!"\nSubpats:\n Idx {sams.subpat.1}\nPats: {← sams.subpat.2.pp (← getLCtx) (← getLocalInstances) [] 0 intersect empty?}\nThms {sams.subpat.3.map String.fromUTF8!}"
  IO.println "\nConjecturable:"
  sams.conj.foldM () (fun n v _ => do
      IO.println s!"\nTheorem: {String.fromUTF8! n}"
      IO.println s!"G idx {v.1} H idx {v.2} Dict {v.3}"
      IO.println s!"Gs: {← v.4.pp (← getLCtx) (← getLocalInstances) [] 0 intersect empty?}"
      IO.println s!"Hs: {← v.5.pp (← getLCtx) (← getLocalInstances) [] 0 intersect empty?}"
      IO.println "\nPatterns:"
      let mut i := 0
      for p in v.6 do
        IO.println s!"\nIndex {i} total {p.1}\nGs: {← p.2.pp (← getLCtx) (← getLocalInstances) [] 0 intersect empty?}"
        i := i+1
      )
  -- not freeing the pickle

#check 1

unsafe def explore_samClass_gh_core_S
  (mod : Name)
  : MetaM Unit :=
    explore_samClass_gh_core
      UInt32Array.inter UInt32Array.isEmpty mod

#check 1

unsafe def explore_gen_thm_core
  {IdxCollType : Type} [Repr IdxCollType]
  (intersect : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (mod : Name)
  : MetaM Unit := do
  let cachePath ← findLeanGrowCacheDir
  let loadpath := FilePath.join cachePath ((FilePath.toString (LeanGrow.sampleNameOfModuleName_thmKey mod)))
  let (sams,reg) ← unpickle (scoreThmKey IdxCollType) loadpath
  IO.println s!"Sample name : {sams.sampleName}"
  IO.println s!"\nLevelNum : {sams.levelNum}"
  IO.println "\nTypes:"
  let mut i := 0
  for T in sams.types do
    IO.println s!"{i} : {← ppExpr T}"
    i := i+1
  let l1 := (← getLCtx)
  let l2 := (← getLocalInstances)
  IO.println "\nRegular back:"
  sams.regularBack.foldM () (fun n v _ => do
      IO.println s!"\nTheorem: {String.fromUTF8! n}"
      IO.println s!"Goals: {← v.goalPain.pp l1 l2 [] 0 intersect empty?}"
      IO.println s!"Goal weights {v.goalWeights.mapIdx Prod.mk}"
      IO.println s!"Hyps: {← v.hypSetTrie.pp 0 (fun p => p.pp l1 l2 [] 0 intersect empty?) (fun (x,y) => return s!"Idx {x}, weight {y}")}"
      )
  IO.println "\nRegular forward:"
  sams.regularForw.foldM () (fun n v _ => do
      IO.println s!"\nTheorem: {String.fromUTF8! n}"
      IO.println s!"Goals: {← v.goalPain.pp l1 l2 [] 0 intersect empty?}"
      IO.println s!"Goal weights {v.goalWeights.mapIdx Prod.mk}"
      IO.println s!"Hyps: {← v.hypSetTrie.pp 0 (fun p => p.pp l1 l2 [] 0 intersect empty?) (fun (x,y) => return s!"Idx {x}, weight {y}")}"
      )
  IO.println "\nSubpats:"
  sams.subpat.foldM () (fun n v _ => do
      IO.println s!"\nTheorem: {String.fromUTF8! n}"
      IO.println s!"Subpatterns: {← v.1.pp l1 l2 [] 0 intersect empty?}"
      IO.println s!"Weights {v.2.mapIdx Prod.mk}"
      )
  IO.println "\nConjecturable:"
  sams.conj.foldM () (fun n (.mk v _ pats) _ => do
      IO.println s!"\nTheorem: {String.fromUTF8! n}"
      IO.println s!"Goals: {← v.goalPain.pp l1 l2 [] 0 intersect empty?}"
      IO.println s!"Goal weights {v.goalWeights.mapIdx Prod.mk}"
      IO.println s!"Hyps: {← v.hypSetTrie.pp 0 (fun p => p.pp l1 l2 [] 0 intersect empty?) (fun (x,y) => return s!"Idx {x}, weight {y}")}"
      IO.println "\nPatterns:"
      let mut i := 0
      for p in pats do
        IO.println s!"\nIndex {i}"
        p.foldlM () (fun th w _ => do
          IO.println s!"Pat: {← ppExpr th.goal}\nHyps: {← th.hypsTypes.mapM ppExpr}\nWeight: {w}"
          )
        i := i+1
      )
  -- not freeing the pickle

#check 1

unsafe def explore_gen_thm_core_S
  (mod : Name)
  : MetaM Unit :=
    explore_gen_thm_core
      UInt32Array.inter UInt32Array.isEmpty mod

#check 1

unsafe def explore_gen_gh_core
  {IdxCollType : Type} [Repr IdxCollType]
  (intersect : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (mod : Name)
  : MetaM Unit := do
  let cachePath ← findLeanGrowCacheDir
  let loadpath := FilePath.join cachePath ((FilePath.toString (LeanGrow.sampleNameOfModuleName_thmKey mod)))
  let (sams,reg) ← unpickle (scoreGHKey IdxCollType) loadpath
  IO.println s!"Sample name : {sams.sampleName}"
  IO.println s!"\nLevelNum : {sams.levelNum}"
  IO.println "\nTypes:"
  let mut i := 0
  for T in sams.types do
    IO.println s!"{i} : {← ppExpr T}"
    i := i+1
  let l1 := (← getLCtx)
  let l2 := (← getLocalInstances)
  IO.println "\nRegular back:"
  IO.println s!"\nGoals: {← sams.regularBack.goalPain.pp l1 l2 [] 0 intersect empty?}"
  IO.println s!"Goal weights {sams.regularBack.goalWeights.mapIdx Prod.mk}"
  i := 0
  for entry in sams.regularBack.hypEntries do
    IO.println s!"\nIdx {i}\nHyps: {← entry.hypSetTrie.pp 0 (fun p => p.pp l1 l2 [] 0 intersect empty?) (fun t => return s!"{t.toList}")}"
    IO.println s!"Hyp weights {entry.hypWeights.mapIdx Prod.mk}"
    i := i+1
  IO.println "\nRegular forw:"
  IO.println s!"\nGoals: {← sams.regularForw.goalPain.pp l1 l2 [] 0 intersect empty?}"
  IO.println s!"Goal weights {sams.regularForw.goalWeights.mapIdx Prod.mk}"
  i := 0
  for entry in sams.regularForw.hypEntries do
    IO.println s!"\nIdx {i}\nHyps: {← entry.hypSetTrie.pp 0 (fun p => p.pp l1 l2 [] 0 intersect empty?) (fun t => return s!"{t.toList}")}"
    IO.println s!"Hyp weights {entry.hypWeights.mapIdx Prod.mk}"
    i := i+1
  IO.println "\nSubpats:"
  IO.println s!"\nGoals: {← sams.subpatPain.pp l1 l2 [] 0 intersect empty?}"
  IO.println s!"Goal weights {sams.subpatVal.mapIdx (fun i x => (i, x.toList))}"
  IO.println "\nConjecturable:"
  sams.conj.foldM () (fun n (.mk v _ pats) _ => do
      IO.println s!"\nTheorem: {String.fromUTF8! n}"
      IO.println s!"Goals: {← v.goalPain.pp l1 l2 [] 0 intersect empty?}"
      IO.println s!"Goal weights {v.goalWeights.mapIdx Prod.mk}"
      IO.println s!"Hyps: {← v.hypSetTrie.pp 0 (fun p => p.pp l1 l2 [] 0 intersect empty?) (fun (x,y) => return s!"Idx {x}, weight {y}")}"
      IO.println "\nPatterns:"
      let mut i := 0
      for p in pats do
        IO.println s!"\nIndex {i}"
        p.foldlM () (fun th w _ => do
          IO.println s!"Pat: {← ppExpr th.goal}\nHyps: {← th.hypsTypes.mapM ppExpr}\nWeight: {w}"
          )
        i := i+1
      )
  -- not freeing the pickle

#check 1


unsafe def explore_gen_gh_core_S
  (mod : Name)
  : MetaM Unit :=
    explore_gen_gh_core
      UInt32Array.inter UInt32Array.isEmpty mod

#check 1
