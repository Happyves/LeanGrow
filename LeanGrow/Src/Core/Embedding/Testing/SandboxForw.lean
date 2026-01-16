/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrowBeta.Core.Embedding.Sandbox
import Mathlib.Data.List.Dedup



set_option linter.style.longLine false

open Lean Meta

#check embedForwIncludeMain
#print ModuleCacheState

#check 1

@[specialize]
def embedForwIncludeMainS
  (l1 : LocalContext) (l2 : LocalInstances)
  (data : ModuleCacheState (List Nat)) (unode? : Nat → Bool)
  (thmembedForwData : CTrie (Array ThmFormat))
  (Q : IntroTree (List Nat)) :=
  @embedForwIncludeMain (List Nat) thmembedForwData _ id
    (fun i => let j := data.stdForwSetTrie_idxToThmIdx[i]! ; data.thm_data[j]!)
    (fun n =>
      match data.thmNameToHypIdx.find? n.toString.toUTF8 with
      | .none => []
      | .some ids => ids)
    unode?
    (List.orderedIntersect) (List.orderedUnion) (List.orderedDiff) List.isEmpty []
    l1 l2 Q
    data.stdForwSetTrie



def testForw
  : LocalContext → LocalInstances → ModuleCacheState (List Nat) → Array (List LocalDecl) → IntroTree (List Nat) → (Nat → Bool) → PaIn (List Nat) → Array Expr → MetaM Unit :=
  fun l1 l2 data _ IT unode? _ _ => do
    let modname := `Sandbox
    let thmData : CTrie (Array ThmFormat) := CTrie.empty.insert modname.toString.toUTF8 data.thm_data
    -- IO.println s!"Sanity: {← data.stdForwSetTrie.pp 0 (fun x => do x.ppS (← getLCtx) (← getLocalInstances) [] 0) (fun x => return s!"{(repr x.name)}")}"
    let res ← embedForwIncludeMainS l1 l2 data
                unode? thmData IT
    IO.println s!"[testForwRW] res inds {res.foldl [] (fun x _ _ L => x :: L)}"
    let final ← embedForwIncludePostProcess l1 l2 res
    IO.println "[testForwRW] success of testForw"
    withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
      final.foldlM () (fun term _ gunids _ => do
        -- the second arg will be used for scoring
        IO.println s!"[testForwRW] proof term ↓ with type ↓↓"
        IO.println s!"[testForwRW] term: {← ppExpr term}"
        IO.println s!"[testForwRW] type: {← ppExpr <| ← inferType term}"
        IO.println s!"[testForwRW] introtree sink gunids : {gunids}")







#check List.dedup_nil
#check List.dedup_cons_of_mem'
#check List.dedup_sublist
#check List.dedup_subset
#check List.dedup_eq_cons
#check List.Nodup.dedup
#check List.Perm.dedup
#check List.Subset.dedup_append_right

def SB : Array Name := #[`List.dedup_sublist, `List.dedup_subset, `List.Perm.dedup]


-- #exit

-- tracing_mode .std
-- tracing_flags [(`embedForwIncludeMain.go, TracingFlags.all),(`embedForwIncludeMain.findSplit, TracingFlags.all)]

-- #exit

With gnodes (l : List Nat) and unodes and tnodes and objects and spicyIntroTree false and sandbox SB run testForw


With gnodes (l : List Nat) (L : List Nat) and unodes and tnodes and objects and spicyIntroTree false and sandbox SB run testForw


With gnodes and unodes (l : List Nat : []) and tnodes and objects and spicyIntroTree false and sandbox SB run testForw

With gnodes (l : List Nat) (h : l.Perm l) and unodes and tnodes and objects and spicyIntroTree false and sandbox SB run testForw


With gnodes (l : List Nat) (L : List Nat) (h : L.Perm l) and unodes and tnodes and objects and spicyIntroTree false and sandbox SB run testForw

With gnodes (h : ([] : List Nat).Perm []) and unodes and tnodes and objects and spicyIntroTree false and sandbox SB run testForw


theorem help (l: List Nat) : l.Perm l := by
  induction' l with x l ih
  · apply List.Perm.nil
  · apply List.Perm.cons
    exact ih

With gnodes and unodes (l : List Nat : [1,2,3]) (h : l.Perm l : help l) and tnodes and objects and spicyIntroTree false and sandbox SB run testForw


With gnodes (n : Nat) and unodes and tnodes and objects and spicyIntroTree false and sandbox SB run testForw
-- negative example, shouldn't find anything in this sandbox

With gnodes (α : Type) (i : DecidableEq α) (l : List α) and unodes and tnodes and objects and spicyIntroTree false and sandbox SB run testForw
-- fails because instance synthesis doesn't consider fvars (that aren't declared as instances) from ltx ??


#check SetTrie.pp
