
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Data.SetTrie.Types
import LeanGrow.Src.Data.Amalgames
import LeanGrow.Src.Utils.Std.String
import LeanGrow.Src.Utils.Tracing
import Lean.Meta.Basic

open Lean Meta

variable {α β : Type _} {m} [Monad m]


@[inline]
def SetTrie.initial (l : List (β × α)) : SetTrie α β :=
  .root (l.mapTRR (fun (xb,xa) => .node xb [.leaf xa]))


@[specialize]
def List.foldOnKeys {γ : Type _} (c : List (SetTrie α β)) (init : γ) (merge : β → γ → γ) : γ :=
  match c with
  | [] => init
  | .node k _ :: rest => rest.foldOnKeys (merge k init) merge
  | .root _ :: rest | .leaf _ :: rest => rest.foldOnKeys init merge


@[specialize]
def List.foldOnKeysM {γ : Type _} (c : List (SetTrie α β)) (init : γ) (merge : β → γ → m γ) : m γ := do
  match c with
  | [] => return init
  | .node k _ :: rest => rest.foldOnKeysM (← merge k init) merge
  | .root _ :: rest | .leaf _ :: rest => rest.foldOnKeysM init merge


@[specialize]
def List.foldOnKeysMcps {γ δ: Type _} (c : List (SetTrie α β)) (init : γ)
  (merge : β → γ → (γ → m δ) → m δ) (K : γ → m δ) : m δ := do
  match c with
  | [] => K init
  | .node k _ :: rest =>
      merge k init <| fun nx => do
        rest.foldOnKeysMcps nx merge K
  | .root _ :: rest | .leaf _ :: rest =>
      rest.foldOnKeysMcps init merge K


@[specialize]
def List.split_on_split {γ : Type _}
  (find : β → γ → Bool) (delete : β → γ → β) (empty? : β → Bool)
  (c : List (SetTrie α β)) (key : γ)
  : List (SetTrie α β) × List (SetTrie α β) :=
    let rec @[specialize] go (pos neg : List (SetTrie α β)) : List (SetTrie α β) → List (SetTrie α β) × List (SetTrie α β)
      | [] => (pos,neg)
      | x@(.root _ ):: more | x@(.leaf _) :: more => go pos (x :: neg) more
      | x@(.node k c) :: more =>
          if find k key
          then
            let nk := (delete k key)
            if empty? nk
            then go (c ++ pos) neg more
            else go ((.node nk c) :: pos) neg more
          else
            go pos (x :: neg) more
    go [] [] c


@[specialize]
def List.split_on_splitMcps {γ ι : Type _}
  (find : β → γ → (Bool → m ι) → m ι) (delete : β → γ → β) (empty? : β → Bool)
  (c : List (SetTrie α β)) (key : γ)
  (K : List (SetTrie α β) → List (SetTrie α β) → m ι) : m ι :=
    let rec @[specialize] go (pos neg : List (SetTrie α β)) : List (SetTrie α β) → m ι
      | [] => K pos neg
      | x@(.root _ ):: more | x@(.leaf _) :: more => go pos (x :: neg) more
      | x@(.node k c) :: more =>
          find k key <| fun res => do
            if res
            then
              let nk := (delete k key )
              if empty? nk
              then go (c ++ pos) neg more
              else go ((.node nk c) :: pos) neg more
            else
              go pos (x :: neg) more
    go [] [] c



@[specialize]
partial def List.splitGreedyMerge
    [Repr α] [Repr β] {γ δ : Type _} [Repr δ] [Repr γ]
    (init : γ) (merge : β → γ → γ) (max : γ → OptionProd δ Nat)
    (find : β → δ → Bool) (delete : β → δ → β) (empty? : β → Bool)
    (newkey : δ → β) (addkey : δ → β → β)
    (c : List (SetTrie α β)) : List (SetTrie α β) :=
      trace set TracingFlags.none in
      let apps := c.foldOnKeys init merge
      trace on .zero with s!"[splitGreedyMerge] apps {repr apps}" in
      match max apps with
      | .none => c
      | .some key M =>
            trace on .zero with s!"[splitGreedyMerge] max key {repr key} at {M} occs." in
            if M > 1
            then
              let (pos, neg) := c.split_on_split find delete empty? key
              trace on .zero with s!"[splitGreedyMerge] pos after split {repr pos}" in
              trace on .zero with s!"[splitGreedyMerge] neg after split {repr neg}" in
              let pos := pos.splitGreedyMerge init merge max find delete empty? newkey addkey
              trace on .zero with s!"[splitGreedyMerge] pos after call {repr pos}" in
              let neg := neg.splitGreedyMerge init merge max find delete empty? newkey addkey
              trace on .zero with s!"[splitGreedyMerge] neg after call {repr neg}" in
              match pos with
              | [.node k vs] =>
                  (SetTrie.node (addkey key k) vs) :: neg
              | _ => (.node (newkey key) pos) :: neg
            else c



@[specialize]
partial def List.splitGreedyMergeMcps  {γ δ κ : Type _}
    (init : γ) (merge : β → γ → (γ → MetaM κ) → MetaM κ)
    (max : γ → OptionProd δ Nat)
    (find : β → δ → (Bool → MetaM κ) → MetaM κ) (delete : β → δ → β) (empty? : β → Bool)
    (newkey : δ → (β → MetaM κ) → MetaM κ) (addkey : δ → β → (β → MetaM κ) → MetaM κ)
    (c : List (SetTrie α β))
    (K : List (SetTrie α β) → MetaM κ) : MetaM κ :=
      c.foldOnKeysMcps init merge <| fun apps => do
        match max apps with
        | .none => K c
        | .some key M =>
              if M > 1
              then
                c.split_on_splitMcps find delete empty? key <| fun pos neg => do
                  pos.splitGreedyMergeMcps init merge max find delete empty? newkey addkey <| fun pos => do
                    neg.splitGreedyMergeMcps init merge max find delete empty? newkey addkey <| fun neg => do
                      match pos with
                      | [.node k vs] =>
                          addkey key k <| fun nx => do
                            K <| (.node nx vs) :: neg
                      | _ =>
                          newkey key <| fun nx => do
                            K <| (.node nx pos) :: neg
              else K c


@[specialize]
partial def SetTrie.cleanFull (T : SetTrie α β) (keyEmpty : β → Bool) (valEq : α → α → Bool) : SetTrie α β :=
  let rec @[inline] help : SetTrie α β → List (SetTrie α β)
    | .root k => k
    | .node _ k => k
    | .leaf .. => []
  match T with
  | .root kids =>
      let kids := (kids.mapTR (fun t => t.cleanFull keyEmpty valEq))
      let (kids,nl) := kids.foldl (fun (R,nl) t =>
        match t with
        | .root .. => panic! "SetTrie.clean, ill formed tree"
        | .leaf v => (R, v :: nl)
        | .node q qs =>
            if keyEmpty q
            then (qs ++ R,nl)
            else (t :: R, nl)
        ) ([], ([] : List α))
      let nl := nl.foldl (fun R x =>
        if @List.contains _ ⟨valEq⟩ R x
        then R
        else x :: R
        ) []
      .root (kids ++ nl.map .leaf)
  | .node k kids =>
      let kids := (kids.mapTR (fun t => t.cleanFull keyEmpty valEq))
      let (kids,nl) := kids.foldl (fun (R,nl) t =>
        match t with
        | .root .. => panic! "SetTrie.clean, ill formed tree"
        | .leaf v => (R, v :: nl)
        | .node q qs =>
            if keyEmpty q
            then (qs ++ R,nl)
            else (t :: R, nl)
        ) ([], ([] : List α))
      let nl := nl.foldl (fun R x =>
        if @List.contains _ ⟨valEq⟩ R x
        then R
        else x :: R
        ) []
      .node k (kids ++ nl.map .leaf)
  | .leaf .. => T


@[specialize]
partial def SetTrie.clean (T : SetTrie α β) (cleanKey : β → β) (keyEmpty : β → Bool) : SetTrie α β :=
  let rec @[inline] help : SetTrie α β → List (SetTrie α β)
    | .root k => k
    | .node _ k => k
    | .leaf .. => []
  match T with
  | .root kids =>
      let kids := (kids.mapTR (fun t => t.clean cleanKey keyEmpty))
      let kids := kids.foldl (fun R t =>
        match t with
        | .root .. => panic! "SetTrie.clean, ill formed tree"
        | .leaf .. => t :: R
        | .node q qs =>
            let q := cleanKey q
            if keyEmpty q
            then qs ++ R
            else (.node q qs) :: R
        ) []
      .root kids
  | .node k kids =>
      let kids := (kids.mapTR (fun t => t.clean cleanKey keyEmpty))
      let kids := kids.foldl (fun R t =>
        match t with
        | .root .. => panic! "SetTrie.clean, ill formed tree"
        | .leaf .. => t :: R
        | .node q qs =>
            let q := cleanKey q
            if keyEmpty q
            then qs ++ R
            else (.node q qs) :: R
        ) []
      .node k kids -- don't clean here, as would clean twice
  | .leaf .. => T



@[specialize]
partial def SetTrie.ofList
    [Repr α] [Repr β] {γ δ : Type _} [Repr δ] [Repr γ]
    (init : γ) (merge : β → γ → γ) (max : γ → OptionProd δ Nat)
    (find : β → δ → Bool) (delete : β → δ → β) (empty? : β → Bool)
    (newkey : δ → β) (addkey : δ → β → β) (cleanKey : β → β)
    (l : ListProd β α) : SetTrie α β :=
    let ini := l.foldl [] (fun k v R => (.node k [.leaf v]) :: R)
    let res := ini.splitGreedyMerge init merge max find delete empty? newkey addkey
    SetTrie.clean (.root res) cleanKey empty?


@[specialize]
partial def SetTrie.ofListMcps {γ δ κ : Type _}
    (init : γ) (merge : β → γ → (γ → MetaM κ) → MetaM κ)
    (max : γ → OptionProd δ Nat)
    (find : β → δ → (Bool → MetaM κ) → MetaM κ) (delete : β → δ → β) (empty? : β → Bool)
    (newkey : δ → (β → MetaM κ) → MetaM κ) (addkey : δ → β → (β → MetaM κ) → MetaM κ)
    (cleanKey : β → β)
    (l : ListProd β α)
    (K : SetTrie α β → MetaM κ) : MetaM κ :=
    let ini := l.foldl [] (fun k v R => (.node k [.leaf v]) :: R)
    ini.splitGreedyMergeMcps init merge max find delete empty? newkey addkey
      <| fun res => K <| SetTrie.clean (.root res) cleanKey empty?



@[specialize]
partial def SetTrie.toList
    (emptykey : β) (mergekey : β → β → β)
    (l : SetTrie α β) : ListProd β α :=
    match l with
    | .root c =>
        c.foldl (fun R t =>
          let res := t.toList emptykey mergekey
          res.foldl R (fun x y z => .cons x y z)
          ) .nil
    | .node k c =>
        c.foldl (fun R t =>
          let res := t.toList emptykey mergekey
          res.foldl R (fun x y z => .cons (mergekey k  x) y z)
          ) .nil
    | .leaf v =>
        .cons emptykey v .nil


@[specialize]
partial def SetTrie.shallowify
    (emptykey : β) (mergekey : β → β → β)
    (l : SetTrie α β) (fuel : Nat) : ListProd β (SetTrie α β) :=
    match l with
    | .root c =>
          c.foldl (fun R t =>
            let res := t.shallowify emptykey mergekey fuel
            res.foldl R (fun x y z => .cons x y z)
            ) .nil
    | .node k c =>
        if fuel == 0
        then .cons emptykey l .nil
        else
          c.foldl (fun R t =>
            let res := t.shallowify emptykey mergekey (fuel - 1)
            res.foldl R (fun x y z => .cons (mergekey k  x) y z)
            ) .nil
    | .leaf .. =>
        .cons emptykey l .nil

@[specialize]
partial def SetTrie.shallowifyTR
    (emptykey : β) (mergekey : β → β → β)
    (l : SetTrie α β) (fuel : Nat) : ListProd β (SetTrie α β) :=
    let rec @[specialize] go (done : ListProd β (SetTrie α β)) : ListProd3 Nat β (SetTrie α β) → ListProd β (SetTrie α β)
      | .nil => done
      | .cons fuel topkey val more =>
          match val with
          | .root c =>
              if fuel == 0
              then
                go (c.foldl (fun R k => .cons topkey k R) done) more
              else
                let nx := c.foldl (fun R k => .cons (fuel - 1) topkey k R) more
                go done nx
          | .node key c =>
              let newkey := (mergekey key topkey)
              if fuel == 0
              then
                go (c.foldl (fun R k => .cons newkey k R) done) more
              else
                let nx := c.foldl (fun R k => .cons (fuel - 1) newkey  k R) more
                go done nx
          | .leaf .. =>
                go (.cons topkey val done) more
    go .nil (.cons fuel emptykey l .nil)



partial def SetTrie.getVals (T : SetTrie α β) : List α :=
  let rec go (done : List α) : List (SetTrie α β) → (List α)
    | [] => done
    | nx :: more =>
        match nx with
        | .leaf a => go (a :: done) more
        | .root c | .node _ c => go done (c ++ more)
  go [] [T]

@[specialize]
partial def SetTrie.pp [Monad m] (ind : Nat) (key : β → m String) (val : α → m String) (T : SetTrie α β) : m String :=
  let rec @[specialize] go (ind : Nat) : SetTrie α β → m String
    | .root kids =>
        return (Blank ind) ++ s!".root\n" ++ (← BlankJumpM (ind +3) kids (fun x => go (ind + 3) x))
    | .node k kids =>
        return (Blank ind) ++ s!".node {← key k}\n" ++ (← BlankJumpM (ind +3) kids (fun x => go (ind + 3) x))
    | .leaf v => return (Blank ind) ++ (← val v)
  go ind T
