

/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrowBeta.Data.SetTrie.Operations
import LeanGrowBeta.Data.CTrie.Operations
import LeanGrowBeta.Data.PathIndex.Operations
import LeanGrowBeta.Data.PathIndex.Insert
import LeanGrowBeta.Data.PathIndex.Indexing
import LeanGrowBeta.Caching.API.PathIndex


open Lean Meta

variable {α : Type _} {m} [Monad m] {IdxCollType : Type _}


-- # PaIn

@[specialize]
def SetTrieP.ofList [Repr α] [Repr IdxCollType]
  (l1 : LocalContext) (l2 : LocalInstances)
  (thmData : CTrie (Array ThmFormat))
  (toList : IdxCollType → List Nat) (hypIndToThm : Nat → ThmFormat)
  (insert intersect union difference : IdxCollType → IdxCollType → IdxCollType)
  (emptyCol : IdxCollType)  (empty? : IdxCollType → Bool) (size : IdxCollType → Nat)
  (l : ListProd (PaIn IdxCollType) α)
  : MetaM (SetTrie α (PaIn IdxCollType)) :=
  trace set TracingFlags.none in
  SetTrie.ofListMcps
    (PaIn.dead, PaIn.dead)
    (fun x (y,z) q => do q (PaIn.merge union emptyCol x y, ← PaIn.mergeLSpe union emptyCol l1 l2 thmData x z))
    (fun (x,y) =>
      trace on .zero with s!"[SetTrieP.ofList] x : {repr x}\n[SetTrieP.ofList] y : {repr y}\n" in
      match y.max intersect empty? size with
      | .none => (OptionProd.none : OptionProd (IdxCollType × (ListProd Expr IdxCollType)) Nat)
      | .some inds m =>
          trace on .zero with s!"[SetTrieP.ofList] inds : {repr inds} ; m {m}\n" in
          let res := PaIn.buildCore x [] 0 (fun x => intersect x inds) intersect empty?
          -- ↑ should be buildIndices
          -- in fact, it should be x with all indices except for inds deleted
          -- so that we pass a PaIn, that we can use in addKey ↓
          let is := res.foldl emptyCol (fun _ i R => union i R)
          OptionProd.some (is, res) m
      )
    (fun x (is,_) q => do
      let real ← x.sharesIndicesWith intersect empty? is
      if real then q (.some ()) else q .none)
    (fun x (is,_) _ => x.deleteOfInds is difference emptyCol empty?)
    (fun x => match x.clean emptyCol empty? with | .dead => true | _ => false)
    (fun (_,es) q => do
          es.foldlMcps PaIn.dead (fun e is T q => do
            for toLoad in (toList is) do
              (hypIndToThm toLoad).mctx.load
            let ⟨res,_,_⟩ ← PaIn.insertMulti l1 l2 e is T emptyCol insert
            q res) <| fun res => q res)
        (fun (_,es) τ q => do -- if es was A Pain, we could simply merge here
          es.foldlMcps τ (fun e is T q => do
            for toLoad in (toList is) do
              (hypIndToThm toLoad).mctx.load
            let ⟨res,_,_⟩ ← PaIn.insertMulti l1 l2 e is T emptyCol insert
            q res) <| fun res => q res)
    l
    (fun x => return x) -- cps is debt from alpha


#check SetTrie.mergeMcps


@[specialize]
def SetTrieP.merge [Repr α] [Repr IdxCollType]
  (l1 : LocalContext) (l2 : LocalInstances)
  (thmData : CTrie (Array ThmFormat))
  (toList : IdxCollType → List Nat) (hypIndToThm : Nat → ThmFormat)
  (insert intersect union difference : IdxCollType → IdxCollType → IdxCollType)
  (emptyCol : IdxCollType)  (empty? : IdxCollType → Bool) (size : IdxCollType → Nat)
  (fuel : Nat) (fst snd : SetTrie α (PaIn IdxCollType))
  : MetaM (SetTrie α (PaIn IdxCollType)) :=
    SetTrie.mergeMcps
      (PaIn.dead, PaIn.dead)
      (fun x (y,z) q => do q (PaIn.merge union emptyCol x y, ← PaIn.mergeLSpe union emptyCol l1 l2 thmData x z))
      (fun (x,y) =>
        match y.max intersect empty? size with
        | .none => .none
        | .some inds m =>
            let res := PaIn.buildCore x [] 0 (fun x => intersect x inds) intersect empty?
            let is := res.foldl emptyCol (fun _ i R => union i R)
            .some (is, res) m
        )
      (fun x (is,_) q => do
        let real ← x.sharesIndicesWith intersect empty? is
        if real then q (.some ()) else q .none)
      (fun x (is,_) _ => x.deleteOfInds is difference emptyCol empty?)
      (fun x => match x.clean emptyCol empty? with | .dead => true | _ => false)
      (fun (_,es) q => do
        es.foldlMcps PaIn.dead (fun e is T q => do
        match (toList is) with
        | [] =>
            let ⟨res,_,_⟩ ← PaIn.insertMulti l1 l2 e is T emptyCol insert
            q res
        | toLoad :: _ => -- `e` can only have lnodes from a single theroem if any
            (hypIndToThm toLoad).mctx.load
            let ⟨res,_,_⟩ ← PaIn.insertMulti l1 l2 e is T emptyCol insert
            q res) <| fun res => q res)
      (fun (_,es) τ q => do
        es.foldlMcps τ (fun e is T q => do
        match (toList is) with
        | [] =>
            let ⟨res,_,_⟩ ← PaIn.insertMulti l1 l2 e is T emptyCol insert
            q res
        | toLoad :: _ => -- `e` can only have lnodes from a single theroem if any
            (hypIndToThm toLoad).mctx.load
            let ⟨res,_,_⟩ ← PaIn.insertMulti l1 l2 e is T emptyCol insert
            q res) <| fun res => q res)
      PaIn.dead
      (PaIn.merge union emptyCol)
      fuel
      fst
      snd
      (fun x => return x) -- cps is debt from alpha
