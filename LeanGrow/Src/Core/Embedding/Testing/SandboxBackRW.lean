/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrowBeta.Core.Embedding.Sandbox
import Mathlib.Data.List.Dedup

set_option linter.style.longLine false


open Lean Meta

def testBackRW
  : LocalContext → LocalInstances → ModuleCacheState (List Nat) → Array (List LocalDecl) → IntroTree (List Nat) → (Nat → Bool) → PaIn (List Nat) → Array Expr → MetaM Unit :=
  fun l1 l2 data deps _ _ _ Os => do
    let target := Os[0]!
    let modname := `Sandbox
    let thmData : CTrie (Array ThmFormat) := CTrie.empty.insert modname.toString.toUTF8 data.thm_data
    let ⟨embs,l1,l2⟩ ← embedBackRWMain l1 l2 thmData
      -- List.isEmpty (List.orderedIntersect) (List.orderedUnion) (List.orderedDiff) [] id
      (data.rwBackPaIn.getIndicesS) 2 [] target data.rwBackPaIn
    embs.foldlMcps () (fun ind embz _ q => do
      IO.println s!"[testBackRW] looking at {repr ind}"
      let thm := data.thm_data[ind]!
      IO.println s!"[testBackRW] associated to thm {repr thm.name}"
      embz.foldlMcps () (fun emb dirs extV S q => do
        embedBackProcess l1 l2 thm emb
          (do IO.println "[testBackRW] failure of embedBackProcess" ; q S)
          (fun _ arg_lvls todo_lvls arg_exprs todo_expr => do
            IO.println "[testBackRW] success of embedBackProcess"
            embedBackRWPreIntegrate
              (fun _ => true) l1 l2 deps dirs -- **todo** have a proper introAdmissible based of the introtree
              666 target extV thm arg_lvls todo_lvls arg_exprs todo_expr
                (fun _ _ => do IO.println "[testBackRW] failure of embedBackRWPreIntegrate" ; q S)
                (fun term count l1 l2 => do
                  IO.println "[testBackRW] success of embedBackPreIntegrate"
                  IO.println s!"[testBackRW] proof term ↓ with type ↓↓"
                  IO.println s!"[testBackRW] term: {← PpExpr term l1 l2}"
                  IO.println s!"[testBackRW] type: {← PpExpr (← InferType term l1 l2) l1 l2}"
                  IO.println s!"[testBackRW] newgoal : {← PpExpr (← InferType (.fvar ⟨tnode 666 (count-1)⟩) l1 l2) l1 l2}"
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

def SB : Array Name := #[`List.dedup_nil, `List.dedup_cons_of_mem',
  `List.dedup_eq_cons, `List.Nodup.dedup, `List.Subset.dedup_append_right,
  `List.length_append]

-- tracing_mode .std
-- -- tracing_flags [(`embedBackProcess, TracingFlags.all), (`embedBackRWMain, TracingFlags.all)]
-- tracing_flags [(`embedBackRWPreIntegrate, TracingFlags.all)]


-- #exit

With gnodes and unodes and tnodes and objects (([] : List Nat) = []) and spicyIntroTree false and sandbox SB run testBackRW
-- works, with the same bizare index out of bounds error that is recovered from, to yield the two correct rewrites

With gnodes (l : List Nat) (L : List Nat) and unodes and tnodes and objects (l.dedup = 0 :: L) and spicyIntroTree false and sandbox SB run testBackRW

-- ↑ works but ↓ doesn't recognize the application of `dedup_eq_cons` because the
-- unode was replaced by its value in the eq term, so that the motive doesn't get
-- factored properly ; a solution would be to use defeq in `Expr.abstractPatTR` instead of ==

With gnodes (l : List Nat) and unodes (L : List Nat : l++l) and tnodes and objects (l.dedup = 0 :: L) and spicyIntroTree false and sandbox SB run testBackRW

-- With gnodes and unodes and tnodes (l : List Nat) and objects (l.dedup = []) and spicyIntroTree false and sandbox SB run testBackRW
-- works but index out of bounds due to same reason as before : buildMVarifyCore and mvar loading, it seems
-- The application of `dedup_nil` where the tnode gets assigned `[]` fails, because the latter
-- contains a universe lnode, as can be seen in traces , at location`[embedTnodes] looking at e []`

With gnodes and unodes and tnodes and objects ((fun x : List Nat => x.dedup) [] = []) and spicyIntroTree false and sandbox SB run testBackRW


With gnodes (l : List Nat) (x : Fin l.length) and unodes and tnodes and objects (x.val = 42) and spicyIntroTree false and sandbox SB run testBackRW
