/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Data.SetTrie.Build


instance {α : Type _} [I : Inhabited α] (IdxCollType : Type u) (PaIn : Type u → Type u) : Inhabited (SetTrieP α IdxCollType PaIn) where
  default := .leaf I.default


@[inline, specialize]
partial def SetTrieP.mk
  {α : Type _} [Inhabited α]
  {IdxCollType : Type u}
  {PaIn : Type u → Type u}
  (merge : (PaIn IdxCollType) → (PaIn IdxCollType) → (PaIn IdxCollType)) (empty : (PaIn IdxCollType))
  (getInds : (PaIn IdxCollType) → IdxCollType)
  (T : SetTrie α (PaIn IdxCollType)) : SetTrieP α IdxCollType PaIn :=
  let rec @[specialize] go [Inhabited α] : SetTrie α (PaIn IdxCollType) → SetTrieP α IdxCollType PaIn
    | .root c =>
        let K := c.foldOnKeys empty merge
        .root K (c.toArray.map go)
    | .node q c =>
        let is := getInds q
        let K := c.foldOnKeys empty merge
        .node is K (c.toArray.map go)
    | .leaf v => .leaf v
  go T

-- # Query

@[inline]
partial def SetTrieP.depth (T : SetTrieP α IdxCollType PaIn) : Nat :=
  let rec go (candidates : List Nat) (depth : Nat) : List (SetTrieP α IdxCollType PaIn) → Nat
    | [] => depth
    | t :: ts =>
        match t with
        | .leaf _ =>
            match candidates with
            | n :: more => go more (if n > depth then n else depth) ts
            | _ => 0
        | .root _ c | .node _ _ c =>
            match candidates with
            | n :: more =>
                go ((List.replicate c.size (n+1)) ++ more) depth (c.foldl (fun x y => x.cons y) ts)
            | _ => 0
  go [0] 0 [T]


@[inline, specialize]
partial def SetTrieP.query [Repr IdxCollType]
  (containedIn : PaIn IdxCollType → PaIn IdxCollType → IdxCollType) (subsetOf : IdxCollType → IdxCollType → Bool)
  (Q : PaIn IdxCollType) (T : SetTrieP α IdxCollType PaIn) : List α :=
  trace set TracingFlags.none in
  let rec @[specialize] go (done : List α) : List (SetTrieP α IdxCollType PaIn) → List α
    | [] => done
    | nx :: more =>
        match nx with
        | .root K c | .node _ K c =>
            let I := containedIn K Q
            trace on .zero with s!"[query] root, containedIn {repr I}" in
            let next := c.foldl (fun nx k =>
              match k with
              | .leaf .. => k :: nx
              | .node key .. => if subsetOf key I then k :: nx else nx
              | .root .. => panic! s!"[query] ill formed tree"
              ) more
            go done next
        | .leaf a => go (a :: done) more
  go [] [T]

@[inline, specialize]
partial def SetTrieP.queryPass [Repr IdxCollType]
  (containedIn : PaIn IdxCollType → PaIn IdxCollType → IdxCollType) (subsetOf : IdxCollType → IdxCollType → Bool)
  (Q : PaIn IdxCollType) (T : SetTrieP α IdxCollType PaIn) : List α × List (SetTrieP α IdxCollType PaIn) :=
  trace set TracingFlags.none in
  let rec @[specialize] go (done : List α) (ret : List (SetTrieP α IdxCollType PaIn)) : List (SetTrieP α IdxCollType PaIn) → List α × List (SetTrieP α IdxCollType PaIn)
    | [] => (done, ret)
    | nx :: more =>
        match nx with
        | .root K c | .node _ K c =>
            let I := containedIn K Q
            trace on .zero with s!"[query] root, containedIn {repr I}" in
            let next := c.foldl (fun (nx,nr) k =>
              match k with
              | .leaf .. => (k :: nx,nr)
              | .node key .. => if subsetOf key I then (k :: nx,nr) else (nx, k :: nr)
              | .root .. => panic! s!"[query] ill formed tree"
              ) (more, ret)
            go done next.2 next.1
        | .leaf a => go (a :: done) ret more
  go [] [] [T]

open Lean Meta

@[inline, specialize]
partial def SetTrieP.queryPassNotifyM [Repr IdxCollType]
  (containedIn : PaIn IdxCollType → PaIn IdxCollType → β → MetaM (IdxCollType × β)) (subsetOf : IdxCollType → IdxCollType → Bool)
  (ini : β) (Q : PaIn IdxCollType) (T : SetTrieP α IdxCollType PaIn) : MetaM (Prod4 Bool (List α) (List (SetTrieP α IdxCollType PaIn)) β) :=
  trace set TracingFlags.none in
  let rec @[specialize] go (done : List α) (ret : List (SetTrieP α IdxCollType PaIn)) (prog? : Bool) (state : β)
    : List (SetTrieP α IdxCollType PaIn) → MetaM (Prod4 Bool (List α) (List (SetTrieP α IdxCollType PaIn)) β)
    | [] => return .mk prog? done ret state
    | nx :: more =>
        match nx with
        | .root K c | .node _ K c => do
            let (I,state) ← containedIn K Q state
            trace on .zero with s!"[query] root, containedIn {repr I}" in
            let s := more.length
            let next := c.foldl (fun (nx,nr) k =>
              match k with
              | .leaf .. => (k :: nx,nr)
              | .node key .. => if subsetOf key I then (k :: nx,nr) else (nx, k :: nr)
              | .root .. => panic! s!"[query] ill formed tree"
              ) (more, ret)
            go done next.2 (if prog? then true else next.1.length > s) state next.1
        | .leaf a => go (a :: done) ret prog? state more
  go [] [] false ini [T]


-- # Map

@[specialize]
partial def SetTrieP.map
  [Inhabited γ] (mapV : α → γ) (mapI : IdxCollType → IdxCollType) (mapK : PaIn IdxCollType → PaIn IdxCollType)
  (T : SetTrieP α IdxCollType PaIn) : SetTrieP γ IdxCollType PaIn :=
    match T with
    | .root keys c => .root (mapK keys) (c.map (fun x => x.map mapV mapI mapK))
    | .node inds keys c => .node (mapI inds) (mapK keys) (c.map (fun x => x.map mapV mapI mapK))
    | .leaf a => .leaf <| mapV a

@[specialize]
partial def SetTrieP.mapM
  [Inhabited γ] (mapV : α → MetaM γ) (mapI : IdxCollType → IdxCollType) (mapK : PaIn IdxCollType → PaIn IdxCollType)
  (T : SetTrieP α IdxCollType PaIn) : MetaM (SetTrieP γ IdxCollType PaIn) :=
    match T with
    | .root keys c => return .root (mapK keys) (← c.mapM (fun x => x.mapM mapV mapI mapK))
    | .node inds keys c => return .node (mapI inds) (mapK keys) (← c.mapM (fun x => x.mapM mapV mapI mapK))
    | .leaf a => return .leaf <| ← mapV a



-- # Merge


@[inline, specialize]
partial def SetTrieP.mergeNoJoin
  [Inhabited α ] (merge : PaIn IdxCollType → PaIn IdxCollType → PaIn IdxCollType)
  (fst snd : SetTrieP α IdxCollType PaIn) : SetTrieP α IdxCollType PaIn :=
    match fst, snd with
    | .root fk fc, .root sk sc => .root (merge fk sk) (fc ++ sc)
    | _, _ => panic! "[SetTrieP.mergeNoJoin] ill formed tree(s)"


-- # pp

@[specialize]
partial def SetTrieP.pp [Monad m] [Repr IdxCollType] (ind : Nat) (key : PaIn IdxCollType → m String) (val : α → m String) (T : SetTrieP α IdxCollType PaIn) : m String :=
  let rec @[specialize] go (ind : Nat) : SetTrieP α IdxCollType PaIn  → m String
    | .root k kids =>
        return (Blank ind) ++ s!".root {← key k}\n" ++ (← BlankJumpM (ind +3) kids.toList (fun x => go (ind + 3) x))
    | .node inds k kids =>
        return (Blank ind) ++ s!".node {repr inds} {← key k}\n" ++ (← BlankJumpM (ind +3) kids.toList (fun x => go (ind + 3) x))
    | .leaf v => return (Blank ind) ++ (← val v)
  go ind T
