
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrowBeta.Core.Embedding.Sandbox
import Mathlib.Data.List.Dedup

set_option linter.style.longLine false



open Lean Meta


#check 1

-- 20s to compile
def embedForwRWMainS (l1 : LocalContext) (l2 : LocalInstances) (thmData : CTrie (Array ThmFormat))
  (constr : List Nat) (revCountMax : ℕ) (extWorkas : List FVarId) (E : Expr)
  (T : PaIn (List Nat)) : MetaM (Prod3 (ListProd ℕ (ListProd embedForwRWData rwDirs)) LocalContext LocalInstances) :=
  @PaIn.embedForwRWMain (List Nat) _ _ _ thmData
    List.isEmpty (List.orderedIntersect) (List.orderedUnion) (List.orderedDiff)
    [] id  l1 l2 constr revCountMax extWorkas E T

#check 1

def testForwRW
  : LocalContext → LocalInstances → ModuleCacheState (List Nat) → Array (List LocalDecl) → IntroTree (List Nat) → (Nat → Bool) → PaIn (List Nat) → Array Expr → MetaM Unit :=
  fun l1 l2 data deps _ _ _ Os => do
    let target := Os[0]! -- will have to ge fvar !!
    let modname := `Sandbox
    let thmData : CTrie (Array ThmFormat) := CTrie.empty.insert modname.toString.toUTF8 data.thm_data
    let Target ← inferType target
    let ⟨embs,l1,l2⟩ ← PaIn.embedForwRWMain thmData
      List.isEmpty (List.orderedIntersect) (List.orderedUnion) (List.orderedDiff) [] id
      l1 l2 (data.rwBackPaIn.getIndices [] (List.orderedUnion)) 2 [] Target data.rwBackPaIn
    embs.foldlMcps () (fun ind embz _ q => do
      IO.println s!"[testForwRW] looking at {repr ind}"
      let thm := data.thm_data[ind]!
      IO.println s!"[testForwRW] associated to thm {repr thm.name}"
      embz.foldlMcps () (fun emb dirs S q => do
        embedForwRWProcess l1 l2 thm emb
          (do IO.println "[testForwRW] failure of embedForwRWProcess" ; q S)
          (fun term _ => do
            IO.println "[testForwRW] success of embedForwRWProcess"
            embedForwRWPreIntegrate
              (fun _ => true) deps l1 l2 dirs -- **todo** have a proper introAdmissible based of the introtree
              Target thm target term
                (fun _ _ => do IO.println "[testForwRW] failure of embedForwRWPreIntegrate" ; q S)
                (fun term l1 l2 => do
                  IO.println "[testForwRW] success of embedForwRWPreIntegrate"
                  IO.println s!"[testForwRW] proof term ↓ with type ↓↓"
                  IO.println s!"[testForwRW] term: {← PpExpr term l1 l2}"
                  IO.println s!"[testForwRW] type: {← PpExpr (← InferType term l1 l2) l1 l2}"
                  q S)
            )
        ) q
      ) <| fun s => return s

-- #exit


#check List.dedup_nil
#check List.dedup_cons_of_mem'
#check List.dedup_sublist
#check List.dedup_subset
#check List.dedup_eq_cons
#check List.Nodup.dedup
#check List.Perm.dedup
#check List.Subset.dedup_append_right
#check List.length_append

def SB : Array Name := #[`List.dedup_nil, `List.dedup_cons_of_mem',
  `List.dedup_eq_cons, `List.Nodup.dedup, `List.Subset.dedup_append_right,
  `List.length_append]


With gnodes (l : List Nat) and unodes and tnodes and objects l and spicyIntroTree false and sandbox SB run testForwRW

With gnodes (l : List Nat) (h : l = []) and unodes and tnodes and objects h and spicyIntroTree false and sandbox SB run testForwRW

With gnodes (l : List Nat) (help : l.Nodup) (h : l = []) and unodes and tnodes and objects h and spicyIntroTree false and sandbox SB run testForwRW
-- List.Nodup.dedup not tried because sinks not in goal ??


With gnodes and unodes (l : List Nat : []) and tnodes and objects l and spicyIntroTree false and sandbox SB run testForwRW
-- fails to unfold unodes ...

With gnodes (l : List Nat) (h : (l ++ l).length = 42) and unodes and tnodes and objects h and spicyIntroTree false and sandbox SB run testForwRW

With gnodes (l : List Nat) (h : (fun x : List Nat => (x ++ l).length) l = 42) and unodes and tnodes and objects h and spicyIntroTree false and sandbox SB run testForwRW
