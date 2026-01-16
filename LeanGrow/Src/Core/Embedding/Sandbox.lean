
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrowBeta.Caching.Build
import LeanGrowBeta.Caching.Load

import LeanGrowBeta.Core.Embedding.EmbedProcessBack
import LeanGrowBeta.Core.Embedding.EmbedProcessForwAPI
import LeanGrowBeta.Core.Embedding.EmbedProcessForwRW
import LeanGrowBeta.Core.Embedding.EmbedQueryBack
import LeanGrowBeta.Core.Embedding.EmbedQueryBackRW
import LeanGrowBeta.Core.Embedding.EmbedQueryForwInclude
import LeanGrowBeta.Core.Embedding.EmbedQueryForwRW
import LeanGrowBeta.Core.Embedding.EmbedQueryForwSimple

import LeanGrowBeta.Utils.LeanGrow.TestTools
import LeanGrowBeta.Caching.Sandbox



open Lean Meta



def ListProd.takeTail (n : Nat) {α β : Type _} (l : ListProd α β) : (ListProd α β) × (ListProd α β) :=
  let rec go (taken todo : ListProd α β) : Nat → (ListProd α β) × (ListProd α β)
    | 0 => (taken,todo)
    | n+1 =>
      match todo with
      | .nil => (taken,todo)
      | .cons x y more => go (.cons x y taken) more n
  go .nil l n


#check evalExpr

def PaIn.ofListProd! (l1 : LocalContext) (l2 : LocalInstances) (l : ListProd Nat Expr) := PaIn.ofListProd l1 l2 l .dead [] (fun n => [n]) (List.orderedInsertOrLeave) --(List.orderedIntersect) List.isEmpty




open Lean Meta Elab Term Command

elab  "With" "gnodes" gs:("("ident ":" term")")*
      "and" "unodes" us:("("ident ":" term ":" term")")*
      "and" "tnodes" ts:("("ident ":" term")")*
      "and" "objects" os:term,*
      "and" "spicyIntroTree" b:term
      "and" "sandbox" sb:term
      "run" metam:ident : command => unsafe do
  let mut gts : Array Syntax := #[]
  let mut gis : Array Name := #[]
  for c in gs do
    match c.raw with
    | .node _ _ A =>
        gis := gis.push (Syntax.getId A[1]!)
        gts := gts.push A[3]!
    | _ => throwError s!"Unexpected syntax at context {c}, expecting (x : T)"
  let mut uts : Array Syntax := #[]
  let mut uvs : Array Syntax := #[]
  let mut uis : Array Name := #[]
  for c in us do
    match c.raw with
    | .node _ _ A =>
        uis := uis.push (Syntax.getId A[1]!)
        uts := uts.push A[3]!
        uvs := uvs.push A[5]!
    | _ => throwError s!"Unexpected syntax at context {c}, expecting (x : T : V)"
  let mut tts : Array Syntax := #[]
  let mut tis : Array Name := #[]
  for c in ts do
    match c.raw with
    | .node _ _ A =>
        tis := tis.push (Syntax.getId A[1]!)
        tts := tts.push A[3]!
    | _ => throwError s!"Unexpected syntax at context {c}, expecting (x : T)"
  let os := os.getElems.raw
  liftTermElabM do
    let SB ← elabTermAndSynthesize sb (.some <| (Expr.const `Array [.zero]).app (.const `Lean.Name []))
    let SB ← evalExpr (Array Name) ((Expr.const `Array [.zero]).app (.const `Lean.Name [])) SB
    elabAndLoadGTNode `g 0 {} gis gts <| fun Gnodes c trans => do
      elabAndLoadUNode c trans uis uts uvs <| fun Unodes _ trans => do
        elabAndLoadGTNode (.num `t 0) 0 trans tis tts <| fun Tnodes _ trans => do
          let mut Os : Array Expr := #[]
          for o in os do
            let term ← elabTermAndSynthesize o .none
            let tterm := term.onAllSubtermsTR (fun
                | d@(.fvar fid) =>
                    match trans.find? fid.name with
                    | .none => d
                    | .some new => .fvar ⟨new⟩
                | x => x
                )
            Os := Os.push tterm
          IO.println "[Test] made it past loading of context and objects"
          let prespicy ← elabTermAndSynthesize b (.some (.const `Bool []))
          let deps ← mkFakeDepCache Gnodes Unodes
          inSandboxS SB <| fun data => do
            let mut i := 0
            let mut LtxL := .nil
            for g in Gnodes do
              LtxL := .cons i (← inferType g) LtxL
              i := i+1
            let k := i
            for u in Unodes do
              LtxL := .cons i (← inferType u) LtxL
              i := i+1
            let mut j := 0
            let mut goalL := .nil
            for t in Tnodes do
              goalL := .cons j (← inferType t) goalL
              j := j+1
            let spicy ← evalExpr Bool ((.const `Bool [])) prespicy
            if spicy
            then
              let (fst,snd) := ListProd.takeTail 3 LtxL
              let ⟨forwTfst,l1,l2⟩ ← PaIn.ofListProd! (← getLCtx) (← getLocalInstances) fst
              let (snd,thd) := ListProd.takeTail 3 snd
              let ⟨forwTsnd,l1,l2⟩ ← PaIn.ofListProd! l1 l2 snd
              let ⟨forwTthd,l1,l2⟩ ← PaIn.ofListProd! l1 l2 thd
              let ⟨goalT,l1,l2⟩ ← PaIn.ofListProd! l1 l2 goalL
              let forwIT : IntroTree (List Nat) :=
                -- todo : fix goal PaIns
                .node [0] [0,1,2] PaIn.dead forwTfst
                (.cons [1] [3,4,5] (IntroTree.leaf [1] [3,4,5] PaIn.dead forwTsnd)
                  (.cons ((List.range j).erase 0 |>.erase 1) ((List.range (i - 6)).map (· + 6))
                      (.leaf ((List.range j).erase 0 |>.erase 1) ((List.range (i - 6)).map (· + 6)) PaIn.dead forwTthd)
                        .nil))
              let unode? : Nat → Bool := (fun n => k ≤ n)
              let action ← evalConst (LocalContext → LocalInstances → ModuleCacheState (List Nat) → Array (List LocalDecl) → IntroTree (List Nat) → (Nat → Bool) → PaIn (List Nat) → Array Expr → MetaM Unit) (metam.getId)
              action l1 l2 data deps forwIT unode? goalT Os
              IO.println "[loadCacheLists] did main action, freeing caches from memory"
            else
              let ⟨forwT,l1,l2⟩ ← PaIn.ofListProd! (← getLCtx) (← getLocalInstances) LtxL
              let ⟨goalT,l1,l2⟩ ← PaIn.ofListProd! l1 l2 goalL
              let forwIT : IntroTree (List Nat) := .leaf (List.range j) (List.range i) .dead forwT
              let unode? : Nat → Bool := (fun n => k ≤ n)
              let action ← evalConst (LocalContext → LocalInstances → ModuleCacheState (List Nat) → Array (List LocalDecl) → IntroTree (List Nat) → (Nat → Bool) → PaIn (List Nat) → Array Expr → MetaM Unit) (metam.getId)
              action l1 l2 data deps forwIT unode? goalT Os
              IO.println "[loadCacheLists] did main action, freeing caches from memory"


#check IntroTree

#exit






#check 1






#check 1
