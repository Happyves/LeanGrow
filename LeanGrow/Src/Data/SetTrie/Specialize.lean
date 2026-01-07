

/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Data.SetTrie.Operations
import LeanGrow.Src.Data.CTrie.Operations
import LeanGrow.Src.Data.PathIndex.Operations
import LeanGrow.Src.Data.PathIndex.Insert
import LeanGrow.Src.Data.PathIndex.Indexing
import LeanGrow.Src.Data.PathIndexG.Operations
import LeanGrow.Src.Data.PathIndexG.Insert
import LeanGrow.Src.Data.PathIndexG.Indexing
import LeanGrow.Src.Data.SetTrie.SetTrieP

open Lean Meta

variable {α : Type _} {m} [Monad m] {IdxCollType : Type _}

-- # CTrie

def SetTrieT (α : Type _) := SetTrie α (CTrie Unit)

def SetTrieT.ofList [Repr α] (l : ListProd (CTrie Unit) α) : SetTrieT α :=
  SetTrie.ofList
    (CTrie.empty : CTrie Nat)
    (fun t sofar => CTrie.merge_count (CTrie.merge_count_initialise t) sofar)
    CTrie.find_max
    (fun x y => (x.find? y).isSome)
    CTrie.delete
    (fun ct => ct.toList.isEmpty)
    (fun key => CTrie.insert .empty key ())
    (fun key T => CTrie.insert T key ())
    l

def SetTrieT.query (Q : CTrie Unit) (T : SetTrieT α) : List α :=
  trace set TracingFlags.none in
  SetTrie.query (fun Q t =>
    let cc := CTrie.CountCommon t Q
    let st := CTrie.size t
    trace on .zero with s!"[SetTrieT.query] cc {cc}, st {st}" in
    cc == st) Q T


-- # PaIn (no loading)


@[specialize]
def SetTriePnG.ofList [Inhabited α] [Repr α] [Repr IdxCollType]
  (intersect union difference : IdxCollType → IdxCollType → IdxCollType)
  (emptyCol : IdxCollType)  (empty? : IdxCollType → Bool) (size : IdxCollType → Nat)
  (l : ListProd (PaIn IdxCollType) α)
  : SetTrieP α IdxCollType PaIn :=
  trace set TracingFlags.none in
  let res := SetTrie.ofList
    PaIn.dead
    (fun x y => PaIn.merge union emptyCol x y)
    (fun x =>
      trace on .zero with s!"[SetTrieP.ofList] x : {repr x}\n[SetTrieP.ofList] y : {repr y}\n" in
      match x.max intersect empty? size with
      | .none => OptionProd.none
      | .some inds m =>
          trace on .zero with s!"[SetTrieP.ofList] inds : {repr inds} ; m {m}\n" in
          let res := x.keepOnlyOfInds inds difference union emptyCol empty?
          -- ↑ should be buildIndices
          -- in fact, it should be x with all indices except for inds deleted
          -- so that we pass a PaIn, that we can use in addKey ↓
          let is := res.getIndices emptyCol union
          OptionProd.some (is, res) m
      )
    (fun x (is,_) => x.sharesIndicesWith intersect empty? is)
    (fun x (is,_) => x.deleteOfInds is difference emptyCol empty?)
    (fun x => match x.clean emptyCol empty? with | .dead => true | _ => false)
    (fun (_,es) => es)
    (fun (_,es) τ => PaIn.merge union emptyCol es τ)
    l
  SetTrieP.mk (PaIn.merge union emptyCol) .dead (PaIn.getIndices emptyCol union) res

@[specialize]
def SetTriePG.ofList [Inhabited α] [Repr α] [Repr IdxCollType]
  (intersect union difference : IdxCollType → IdxCollType → IdxCollType)
  (emptyCol : IdxCollType)  (empty? : IdxCollType → Bool) (size : IdxCollType → Nat)
  (l : ListProd (PaInG IdxCollType) α)
  : SetTrieP α IdxCollType PaInG :=
  trace set TracingFlags.none in
  let res := SetTrie.ofList
    PaInG.dead
    (fun x y => PaInG.merge union emptyCol x y)
    (fun x =>
      trace on .zero with s!"[SetTrieP.ofList] x : {repr x}\n[SetTrieP.ofList] y : {repr y}\n" in
      match x.max intersect empty? size with
      | .none => OptionProd.none
      | .some inds m =>
          trace on .zero with s!"[SetTrieP.ofList] inds : {repr inds} ; m {m}\n" in
          let res := x.keepOnlyOfInds inds difference union emptyCol empty?
          -- ↑ should be buildIndices
          -- in fact, it should be x with all indices except for inds deleted
          -- so that we pass a PaIn, that we can use in addKey ↓
          let is := res.getIndices emptyCol union
          OptionProd.some (is, res) m
      )
    (fun x (is,_) => x.sharesIndicesWith intersect empty? is)
    (fun x (is,_) => x.deleteOfInds is difference emptyCol empty?)
    (fun x => match x.clean emptyCol empty? with | .dead => true | _ => false)
    (fun (_,es) => es)
    (fun (_,es) τ => PaInG.merge union emptyCol es τ)
    l
  SetTrieP.mk (PaInG.merge union emptyCol) .dead (PaInG.getIndices emptyCol union) res
#exit

@[inline, specialize]
partial def SetTriePnG.mergeNoJoin
  [Inhabited α ] (union : IdxCollType → IdxCollType → IdxCollType)
  (emptyCol : IdxCollType)
  (fst snd : SetTrieP α IdxCollType PaIn) : SetTrieP α IdxCollType PaIn :=
    SetTrieP.mergeNoJoin (PaIn.merge union emptyCol) fst snd

@[inline, specialize]
partial def SetTriePG.mergeNoJoin
  [Inhabited α ] (union : IdxCollType → IdxCollType → IdxCollType)
  (emptyCol : IdxCollType)
  (fst snd : SetTrieP α IdxCollType PaInG) : SetTrieP α IdxCollType PaInG :=
    SetTrieP.mergeNoJoin (PaInG.merge union emptyCol) fst snd



#exit

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
