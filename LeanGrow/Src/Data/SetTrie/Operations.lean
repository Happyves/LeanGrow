
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrowBeta.Data.SetTrie.Build

open Lean Meta

variable {α β : Type _} {m} [Monad m]


partial def SetTrie.depth (T : SetTrie α β) : Nat :=
  let rec go (candidates : List Nat) (depth : Nat) : List (SetTrie α β) → Nat
    | [] => depth
    | t :: ts =>
        match t with
        | .leaf _ =>
            match candidates with
            | n :: more => go more (if n > depth then n else depth) ts
            | _ => 0
        | .root c | .node _ c =>
            match candidates with
            | n :: more =>
                go ((List.replicate c.length (n+1)) ++ more) depth (c ++ ts)
            | _ => 0
  go [0] 0 [T]


-- # Query

@[specialize]
partial def SetTrie.query [Repr β]
  (inter : β → β → Bool) (Q : β) (T : SetTrie α β) : List α :=
  trace set TracingFlags.none in
  let rec @[specialize] go (done : List α) : List (SetTrie α β) → List α
    | [] => done
    | nx :: more =>
        match nx with
        | .root c =>
            trace on .zero with s!"[query] root" in
            go done (c ++ more)
        | .node t c =>
            trace on .zero with s!"[query] inter :\nQ:{repr Q}\nt:{repr t}" in
            if inter Q t
            then
              trace on .zero with s!"[query] positive inter" in
              go done (c ++ more)
            else
              trace on .zero with s!"[query] ngative inter" in
              go done more
        | .leaf a => go (a :: done) more
  go [] [T]



@[specialize]
partial def List.queryPass (inter : β → β → Bool) (Q : β) (L : List (SetTrie α β)) : List α × List (SetTrie α β) :=
  let rec @[specialize] go (done : List α) (ret : List (SetTrie α β)) : List (SetTrie α β) → List α × List (SetTrie α β)
    | [] => (done, ret)
    | nx :: more =>
        match nx with
        | .root c => go done ret (c ++ more)
        | .node t c => if inter Q t then go done ret (c ++ more) else go done (nx :: ret) more
        | .leaf a => go (a :: done) ret more
  go [] [] L


@[specialize]
partial def SetTrie.queryM (inter : β → β → m Bool) (Q : β) (T : SetTrie α β) : m (List α) :=
  let rec @[specialize] go (done : List α) : List (SetTrie α β) → m (List α)
    | [] => return done
    | nx :: more => do
        match nx with
        | .root c => go done (c ++ more)
        | .node t c => if ← inter Q t then go done (c ++ more) else go done more
        | .leaf a => go (a :: done) more
  go [] [T]

@[specialize]
partial def List.queryPassM (inter : β → β → MetaM Bool) (Q : β) (L : List (SetTrie α β)) : MetaM (List α × List (SetTrie α β)) :=
  let rec @[specialize] go (done : List α) (ret : List (SetTrie α β)) : List (SetTrie α β) → MetaM (List α × List (SetTrie α β))
    | [] => return (done, ret)
    | nx :: more => do
        match nx with
        | .root c => go done ret (c ++ more)
        | .node t c => if ← inter Q t then go done ret (c ++ more) else go done (nx :: ret) more
        | .leaf a => go (a :: done) ret more
  go [] [] L

@[specialize]
partial def List.queryPassNotifyM (inter : β → β → MetaM Bool) (Q : β) (L : List (SetTrie α β)) : MetaM (Prod3 (List α) (List (SetTrie α β)) Bool) :=
  let rec @[specialize] go (done : List α) (ret : List (SetTrie α β)) (progress? : Bool) : List (SetTrie α β) → MetaM (Prod3 (List α) (List (SetTrie α β)) Bool)
    | [] => return ⟨done, ret,progress?⟩
    | nx :: more => do
        match nx with
        | .root c => go done ret progress? (c ++ more)
        | .node t c => if ← inter Q t then go done ret true (c ++ more) else go done (nx :: ret) progress? more
        | .leaf a => go (a :: done) ret progress? more
  go [] [] false L



@[specialize]
partial def SetTrie.queryMcps {γ : Sort _} (inter : β → β → (Bool → MetaM γ) → MetaM γ)
  (Q : β) (T : SetTrie α β) (k : (List α) → MetaM γ) : MetaM γ :=
  let rec @[specialize] go (done : List α) (k : (List α) → MetaM γ) : List (SetTrie α β) → MetaM γ
    | [] => k done
    | nx :: more => do
        match nx with
        | .root c => go done k (c ++ more)
        | .node t c =>
            inter Q t <| fun res =>
              if res then go done k (c ++ more) else go done k more
        | .leaf a => go (a :: done) k more
  go [] k [T]

@[specialize]
partial def List.queryPassMcps {γ : Sort _}  (inter : β → β → (Bool → MetaM γ) → MetaM γ)
  (Q : β) (L : List (SetTrie α β)) (k : List α → List (SetTrie α β) → MetaM γ) : MetaM γ :=
  let rec @[specialize] go (done : List α) (ret : List (SetTrie α β)) (k : (List α) → List (SetTrie α β) →  MetaM γ) : List (SetTrie α β) → MetaM γ
    | [] => k done ret
    | nx :: more => do
        match nx with
        | .root c => go done ret k (c ++ more)
        | .node t c =>
            inter Q t <| fun res =>
              if res then go done ret k (c ++ more) else go done (nx :: ret) k more
        | .leaf a => go (a :: done) ret k more
  go [] [] k L


@[specialize]
partial def List.queryPassFoldMcps {γ δ : Type _}
  (inter : δ → β → β → (δ → Bool → MetaM γ) → MetaM γ)
  (Q : β) (L : ListProd δ (SetTrie α β))
  (k : ListProd δ α → ListProd δ (SetTrie α β) → MetaM γ) : MetaM γ :=
  let rec @[specialize] go (done : ListProd δ α) (ret : ListProd δ (SetTrie α β)) (k : (ListProd δ α) → ListProd δ (SetTrie α β) →  MetaM γ) : ListProd δ (SetTrie α β) → MetaM γ
    | .nil => k done ret
    | .cons st nx more => do
        match nx with
        | .root c =>
            let nc := c.foldl (fun R x => .cons st x R) more
            go done ret k nc
        | .node t c =>
            inter st Q t <| fun st res =>
              if res
              then
                let nc := c.foldl (fun R x => .cons st x R) more
                go done ret k nc
              else
                go done (.cons st nx ret) k more
        | .leaf a => go (.cons st a done) ret k more
  go .nil .nil k L

@[specialize]
partial def List.queryPassFoldMcpsTop {γ δ : Type _}
  (inter : δ → β → β → (δ → Bool → MetaM γ) → MetaM γ)
  (Q : β) (T : SetTrie α β) (init : δ)
  (k : ListProd δ α → ListProd δ (SetTrie α β) → MetaM γ) : MetaM γ :=
    List.queryPassFoldMcps inter Q (.cons init T .nil) k


-- # Map


/-- Won't preserve order-/
@[specialize]
partial def SetTrie.map {γ δ : Sort _}
  (mapK : β → δ) (mapV : α → γ)
  (T : SetTrie α β) : SetTrie γ δ :=
    match T with
    | .root c => .root (c.mapTRR (fun x => x.map mapK mapV))
    | .node t c => .node (mapK t) (c.mapTRR (fun x => x.map mapK mapV))
    | .leaf a => .leaf <| mapV a



/-- Won't preserve order-/
@[specialize]
partial def SetTrie.mapM {γ δ : Type _}
  (mapK : β → m δ) (mapV : α → m γ)
  (T : SetTrie α β) : m (SetTrie γ δ) :=
    match T with
    | .root c => return .root (← c.mapTRRM (fun x => x.mapM mapK mapV))
    | .node t c => return .node (← mapK t) (← c.mapTRRM (fun x => x.mapM mapK mapV))
    | .leaf a => return .leaf <| ← mapV a




-- # Merge


@[specialize]
partial def SetTrie.merge
  [Repr α] [Repr β] {γ δ ι : Type _} [Repr δ] [Repr γ]
  (init : γ) (merge : β → γ → γ) (max : γ → OptionProd δ Nat)
  (find : β → δ → Option ι) (delete : β → δ → β) (empty? : β → Bool)
  (newkey : δ → β) (addkey : δ → β → β)
  (emptykey : β) (mergekey : β → β → β)
  (fuel : Nat) (fst snd : SetTrie α β) : SetTrie α β :=
    let shallowed := (fst.shallowify emptykey mergekey fuel).foldl (snd.shallowify emptykey mergekey fuel) ListProd.cons
    let stst := SetTrie.ofList init merge max find delete empty? newkey addkey shallowed
    let rec concat : SetTrie (SetTrie α β) β → SetTrie α β
          | .root c => .root <| c.mapTRR concat
          | .node k c => .node k <| c.mapTRR concat
          | .leaf v => v
    concat stst


@[specialize]
partial def SetTrie.mergeMcps
    [Repr α] [Repr β]
    {γ δ ι κ : Type _}
    (init : γ) (merge : β → γ → (γ → MetaM κ) → MetaM κ)
    (max : γ → OptionProd δ Nat)
    (find : β → δ → (Option ι → MetaM κ) → MetaM κ) (delete : β → δ → ι → β) (empty? : β → Bool)
    (newkey : δ → (β → MetaM κ) → MetaM κ) (addkey : δ → β → (β → MetaM κ) → MetaM κ)
    (emptykey : β) (mergekey : β → β → β)
    (fuel : Nat) (fst snd : SetTrie α β)
    (K : SetTrie α β → MetaM κ) : MetaM κ :=
      let rec concat : SetTrie (SetTrie α β) β → SetTrie α β
          | .root c => .root <| c.mapTRR concat
          | .node k c => .node k <| c.mapTRR concat
          | .leaf v => v
      let shallowed := (fst.shallowifyTR emptykey mergekey fuel).foldl (snd.shallowifyTR emptykey mergekey fuel) ListProd.cons
      let (toRoot, toMerge) := shallowed.foldl ([], (.nil : ListProd β (SetTrie α β))) (fun key val (R,M) => if empty? key then (val :: R, M) else (R, .cons key val M))
      SetTrie.ofListMcps init merge max find delete empty? newkey addkey toMerge <| fun stst => do
        match concat stst with
        | .root c => K <| .root (toRoot ++ c)
        | _ => throwError s!"[SetTrie.mergeMcps] ill formed tree ?!?"



-- # Insert

@[inline]
def SetTrie.easyInsert (T : SetTrie α β) (key : β) (val : α) : SetTrie α β :=
  match T with
  | .root kids => .root ((.node key [.leaf val]) :: kids)
  | _ => panic s!"[SetTrie.easyInsert] il formed tree not starting at root"
