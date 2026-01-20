
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Core.Rewriting.Directions
import LeanGrow.Src.Core.Embedding.EmbedQueryBack


open Lean Meta

@[specialize]
def mergeOccsTwo {α : Type _} [ToString α]
  (eq? : α → α → MetaM Bool) (mer : rwDirs → rwDirs → rwDirs)
  (F A : ListProd Nat (ListProd α rwDirs)) :
  MetaM <| ListProd Nat (ListProd α rwDirs) :=
  let rec @[specialize] inner_fst (sofar left : ListProd α rwDirs) : (ListProd α rwDirs) → MetaM (ListProd α rwDirs)
    | .nil => return sofar
    | .cons as ds more => do
      match ← left.findM? (fun x _ => eq? x as) with
      | .none => inner_fst (.cons as (mer .no ds) sofar) left more
      | .some _ mds => inner_fst (.cons as (mer mds ds) sofar) left more
  let rec @[specialize] inner_snd (sofar : ListProd α rwDirs) : ListProd α rwDirs → MetaM (ListProd α rwDirs)
    | .nil => return sofar
    | .cons as ds more => do
      match ← sofar.findM? (fun x _ => eq? x as) with
      | .none => inner_snd (.cons as (mer ds .no) sofar) more
      | .some .. => inner_snd sofar more
  let inner := (fun l r => do inner_snd (← inner_fst .nil l r) l)
  let rec @[specialize] main_fst (res :  ListProd Nat (ListProd α rwDirs)) :  ListProd Nat (ListProd α rwDirs) → MetaM ( ListProd Nat (ListProd α rwDirs))
    | .nil => return res
    | .cons idx data more =>
      match A.find? (fun x  _ => x == idx) with
      | .none =>
        let newdata := data.map (fun x y => (x, (mer y .no)))
        main_fst (.cons idx newdata res) more
      | .some _ odata => do
        let here ← inner data odata
        main_fst (.cons idx here res) more
  let rec @[specialize] main_snd (res :  ListProd Nat (ListProd α rwDirs)) :  ListProd Nat (ListProd α rwDirs) → MetaM ( ListProd Nat (ListProd α rwDirs))
    | .nil => return res
    | .cons idx data more =>
      match res.find? (fun x _ => x == idx) with
      | .none =>
        let newdata := data.map (fun x y => (x, (mer .no y)))
        main_snd (.cons idx newdata res) more
      | .some .. => main_snd res more
  -- trace set Tracing.Flags.none in
  do
  mtracing
  mtrace  on .zero with s!"[mergeOccsTwo] Call on F {repr <| F.map (fun x y => (x, y.map (fun x y => (toString x, y))))} A {repr <| A.map (fun x y => (x, y.map (fun x y => (toString x, y))))}"
  let res ← main_snd (← main_fst .nil F) A
  mtrace  on .zero with s!"[mergeOccsTwo] returning {repr <| res.map (fun x y => (x, y.map (fun x y => (toString x, y))))}"
  return res



@[specialize]
def mergeOnInd {α : Sort _} (join : α → α → α) (X Y : ListProd Nat α) : ListProd Nat α :=
  let rec @[specialize] go (done post : ListProd Nat α) : ListProd Nat α → ListProd Nat α
    | .nil =>
        done.foldl post (fun x y R => .cons x y R)
    | .cons x y xs =>
      match done.find? (fun z _ => z == x) with
      | .none => go done (.cons x y post) xs
      | .some _ val => go (.cons x (join val y) done) (post) xs
  go X .nil Y


@[specialize]
def mergeOnIndSpe {α β : Sort _} (join : α → α → α) (spe : β → α)
  (X : ListProd Nat α) (Y : ListProd Nat β) : ListProd Nat α :=
  let rec @[specialize] go (done post : ListProd Nat α) : ListProd Nat β → ListProd Nat α
    | .nil =>
        done.foldl post (fun x y R => .cons x y R)
    | .cons x y xs =>
      match done.find? (fun z _ => z == x) with
      | .none => go done (.cons x (spe y) post) xs
      | .some _ val => go (.cons x (join val (spe y)) done) (post) xs
  go X .nil Y

variable {IdxCollType : Type}

@[inline]
def defEqWiCommonWorker (l1 : LocalContext) (l2 : LocalInstances)  (A B :  Expr) : MetaM Bool := do
  let go (A B :  Expr) : MetaM Bool := do
    let Aw := A.getWorkerFVarIds
    let B := B.onAllSubtermsTR (fun
      | x@(.fvar w@⟨.num _ p⟩) =>
          if !w.isWorker
          then x
          else
            match Aw.find? (fun | ⟨.num _ j⟩ => p == j | _ => false) with
            | .none => x -- fail
            | .some rep => .fvar rep
      | x => x
      )
    return (← defEqWiMv A B l1 l2).isSome
  if A.hasWorkerTR
  then
    go A B
  else
    return (← defEqWiMv A B l1 l2 ).isSome

@[inline]
def listIndxSingleOut {α : Type _} (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β)
  (l : ListProd IdxCollType α) : ListProd Nat α :=
    l.foldl .nil (fun ids val R =>
      fold ids R (fun i R => .cons i val R))
