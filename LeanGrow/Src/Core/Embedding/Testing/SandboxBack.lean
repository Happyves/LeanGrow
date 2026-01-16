

/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrowBeta.Core.Embedding.Sandbox
import Mathlib.Data.List.Dedup

set_option linter.style.longLine false

open Lean Meta

def testBack
  : LocalContext → LocalInstances → ModuleCacheState (List Nat) → Array (List LocalDecl) → IntroTree (List Nat) → (Nat → Bool) → PaIn (List Nat) → Array Expr → MetaM Unit :=
  fun l1 l2 data _ _ _ _ Os => do
    let target := Os[0]!
    let modname := `Sandbox
    let thmData : CTrie (Array ThmFormat) := CTrie.empty.insert modname.toString.toUTF8 data.thm_data
    let ⟨qase,inds,embs,l1,l2⟩ ← PaIn.embedBackMain l1 l2 thmData
      List.isEmpty (List.orderedIntersect) (List.orderedUnion) (List.orderedDiff) []
      (data.stdBackPaIn.getIndices [] (List.orderedUnion)) 2 [] target data.stdBackPaIn
    if qase == 0
    then
      (IO.println "[testBack] fail 1")
    else if qase == 1
    then
      (IO.println "[testBack] deadC")
    else
      IO.println s!"[testBack] successful query : retuned indices : {repr inds}"
      embs.foldlMcps () (fun inds emb S q => do
        IO.println s!"[testBack] looking at {repr inds}"
        let thm := data.thm_data[inds.head!]!
        IO.println s!"[testBack] associated to thm {repr thm.name}"
        embedBackProcess l1 l2 thm emb
          (do IO.println "[testBack] failure of embedBackProcess" ; q S)
          (fun _ arg_lvls todo_lvls arg_exprs todo_expr => do
            IO.println "[testBack] success of embedBackProcess"
            let ⟨term, _,l1,l2⟩ ← embedBackPreIntegrate l1 l2 thm 666 arg_lvls todo_lvls arg_exprs todo_expr
            IO.println "[testBack] success of embedBackPreIntegrate"
            IO.println s!"[testBack] proof term ↓ with type ↓↓"
            IO.println s!"[testBack] term: {← PpExpr term l1 l2}"
            IO.println s!"[testBack] type: {← PpExpr (← InferType term l1 l2) l1 l2}"
            IO.println s!"[testBack] type correct : {← IsTypeCorrect term l1 l2}"
            q S
            )
        ) <| fun s => return s


#check PaIn.embedBackMain



#check List.dedup_nil
#check List.dedup_cons_of_mem'
#check List.dedup_sublist
#check List.dedup_subset
#check List.dedup_eq_cons
#check List.Nodup.dedup
#check List.Perm.dedup
#check List.Subset.dedup_append_right

def SB : Array Name := #[`List.dedup_sublist, `List.dedup_subset, `List.Perm.dedup]

With gnodes (l : List Nat) and unodes and tnodes and objects (l.dedup ⊆ l) and spicyIntroTree false and sandbox SB run testBack

With gnodes (l : List Nat) and unodes and tnodes and objects ((l++l).dedup ⊆ (l++l)) and spicyIntroTree false and sandbox SB run testBack

With gnodes (l : List Nat) and unodes and tnodes and objects (l.dedup ⊆ ([]++l)) and spicyIntroTree false and sandbox SB run testBack

With gnodes (l : List Nat) and unodes and tnodes and objects (([]++l).dedup ⊆ l) and spicyIntroTree false and sandbox SB run testBack

With gnodes (l : List Nat) and unodes (L : List Nat : []) and tnodes and objects (l.dedup ⊆ (L++l)) and spicyIntroTree false and sandbox SB run testBack

With gnodes (l : List Nat) and unodes (L : List Nat : l ++ l) and tnodes and objects (((l ++ l) ++ l).dedup ⊆ (L++l)) and spicyIntroTree false and sandbox SB run testBack

With gnodes and unodes and tnodes (l : List Nat) and objects (l.dedup ⊆ []) and spicyIntroTree false and sandbox SB run testBack
-- works : note the tnode assignement !


With gnodes (l : List Nat) (L : List Nat) and unodes and tnodes and objects (l.dedup ⊆ L) and spicyIntroTree false and sandbox SB run testBack
-- negative example
