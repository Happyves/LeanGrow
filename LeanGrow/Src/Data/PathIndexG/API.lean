

/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Data.PathIndexG.Types
import LeanGrow.Src.Utils.Std.List

open Lean Meta


variable {α : Type _} (r : α → α → Bool) {IdxCollType : Type _} [BEq α]

@[specialize]
def ListProd.insert_PaInG_core
  (singleton : Nat → IdxCollType) (insert : Nat → IdxCollType → IdxCollType)
  (L : ListProd IdxCollType α) (new : α) (idx : Nat) : ListProd IdxCollType α :=
  let rec @[specialize] go : ListProd IdxCollType α → ListProd IdxCollType α
    | .nil => .cons (singleton idx) new .nil
    | y@(.cons is k more )=>
        if r new k
        then
          if new == k
          then
            .cons (insert idx is) k more
          else
            .cons (singleton idx) new y
        else
          .cons is k (go more)
  go L

@[specialize]
def ListProd.insert_PaInG_core_multi
  (insert : IdxCollType → IdxCollType → IdxCollType)
  (L : ListProd IdxCollType α) (new : α) (idx : IdxCollType) : ListProd IdxCollType α :=
  let rec go : ListProd IdxCollType α → ListProd IdxCollType α
    | .nil => .cons idx new .nil
    | y@(.cons is k more )=>
        if r new k
        then
          if new == k
          then
            .cons (insert idx is) k more
          else
            .cons idx new y
        else
          .cons is k (go more)
  go L


def ListProd.find_PaInG_core
  (L : ListProd IdxCollType α) (new : α) : OptionProd IdxCollType α :=
  let rec @[specialize] go : ListProd IdxCollType α → OptionProd IdxCollType α
    | .nil => .none
    | .cons is k more =>
        if r new k
        then
          if new == k
          then
            .some is k
          else
            .none
        else
          go more
  go L



@[specialize]
def ListProd.insert_PaInG_nat :=
  @ListProd.insert_PaInG_core Nat (fun x y => x ≤ y) IdxCollType inferInstance

@[specialize]
def ListProd.insert_PaInG_nat_multi :=
  @ListProd.insert_PaInG_core_multi Nat (fun x y => x ≤ y) IdxCollType inferInstance


def ListProd.find_PaInG_nat :=
  @ListProd.find_PaInG_core Nat (fun x y => x ≤ y) IdxCollType inferInstance


@[specialize]
def ListProd.insert_PaInG_lex :=
  @ListProd.insert_PaInG_core (Nat × Nat) (fun x y =>
    match compare x.1 y.1 with
    | .lt => true
    | .eq => x.2 ≤ y.2
    | .gt => false
    ) IdxCollType inferInstance

@[specialize]
def ListProd.insert_PaInG_lex_multi :=
  @ListProd.insert_PaInG_core_multi (Nat × Nat) (fun x y =>
    match compare x.1 y.1 with
    | .lt => true
    | .eq => x.2 ≤ y.2
    | .gt => false
    ) IdxCollType inferInstance



def ListProd.find_PaInG_lex :=
  @ListProd.find_PaInG_core (Nat × Nat) (fun x y =>
    match compare x.1 y.1 with
    | .lt => true
    | .eq => x.2 ≤ y.2
    | .gt => false
    ) IdxCollType inferInstance



@[specialize]
def ListProd.modifyAddG {Val Key : Type _} [BEq Key] (mod : Val → Val) (newK : Key) (newV : Val)
  (L : ListProd Val Key) : ListProd Val Key :=
  let rec @[specialize] go : ListProd Val Key → ListProd Val Key
    | .nil => .cons newV newK .nil
    | .cons v k more =>
        if k == newK then .cons (mod v) k more else .cons v k (go more)
  go L

@[specialize, inline]
def ListProd.modifyAddG'G {Val Key : Type _} (atKey : Key → Bool) (modK : Key → Key) (modV : Val → Val) (newK : Key) (newV : Val)
  (L : ListProd Val Key) : ListProd Val Key :=
  let rec @[specialize] go : ListProd Val Key → ListProd Val Key
    | .nil => .cons newV newK .nil
    | .cons v k more =>
        if atKey k then .cons (modV v) (modK k) more else .cons v k (go more)
  go L


@[specialize]
def ListProd.insert_PaInG_const
  (singleton : Nat → IdxCollType) (insert : Nat → IdxCollType → IdxCollType)
  (L : CTrie (ListProd IdxCollType (List Level))) (newN : Name) (newL : List Level) (idx : Nat)
  : CTrie (ListProd IdxCollType (List Level)) :=
  L.upsert newN.toString.toUTF8 (fun
    | .none => .some <| .cons (singleton idx) newL .nil
    | .some E => .some <| E.modifyAddG (fun x => insert idx x) newL (singleton idx)
    )

@[specialize]
def ListProd.insert_PaInG_const_multi
  (insert : IdxCollType → IdxCollType → IdxCollType)
  (L : CTrie (ListProd IdxCollType (List Level))) (newN : Name) (newL : List Level) (idx : IdxCollType)
  : CTrie (ListProd IdxCollType (List Level)) :=
  L.upsert newN.toString.toUTF8 (fun
    | .none => .some <| .cons idx newL .nil
    | .some E => .some <| E.modifyAddG (fun x => insert idx x) newL idx
    )


def ListProd.find_PaInG_const
  (L : CTrie (ListProd IdxCollType (List Level))) (newN : Name) (newL : List Level)
  : OptionProd IdxCollType (List Level) :=
  match L.find? newN.toString.toUTF8 with
  | .none => .none
  | .some D => D.find? (fun _ y => y == newL)



@[specialize]
def ListProd.insert_PaInG_lnode
  (singleton : Nat → IdxCollType) (insert : Nat → IdxCollType → IdxCollType)
  (L : CTrie (ListProd IdxCollType (Nat × Nat))) (newN : Name) (newL : (Nat × Nat)) (idx : Nat)
  : CTrie (ListProd IdxCollType (Nat × Nat)) :=
  L.upsert newN.toString.toUTF8 (fun
    | .none => .some <| .cons (singleton idx) newL .nil
    | .some E => .some <| ListProd.insert_PaInG_lex singleton insert E newL idx
    )

@[specialize]
def ListProd.insert_PaInG_lnode_multi
  (insert : IdxCollType → IdxCollType → IdxCollType)
  (L : CTrie (ListProd IdxCollType (Nat × Nat))) (newN : Name) (newL : (Nat × Nat)) (idx : IdxCollType)
  : CTrie (ListProd IdxCollType (Nat × Nat)) :=
  L.upsert newN.toString.toUTF8 (fun
    | .none => .some <| .cons idx newL .nil
    | .some E => .some <| ListProd.insert_PaInG_lex_multi insert E newL idx
    )

def ListProd.find_PaInG_lnode
  (L : CTrie (ListProd IdxCollType (Nat × Nat))) (newN : Name) (newL : (Nat × Nat))
  : OptionProd IdxCollType (Nat × Nat) :=
  match L.find? newN.toString.toUTF8 with
  | .none => .none
  | .some D => D.find_PaInG_lex newL



@[specialize]
def ListProd.modifyAddGMG
  (l1 : LocalContext) (l2 : LocalInstances)
  {Val Key : Type _} [BEq Key] (L : ListProd Val Key)
  (mod : Val → LocalContext → LocalInstances → MetaM (Prod3 Val LocalContext LocalInstances)) (newK : Key) (newV : Val)
  : MetaM (Prod3 (ListProd Val Key) LocalContext LocalInstances) :=
  let rec @[specialize] go (l1 : LocalContext) (l2 : LocalInstances) (mod? : Bool) (done : ListProd Val Key)
    : ListProd Val Key → MetaM (Prod3 (ListProd Val Key) LocalContext LocalInstances)
    | .nil =>
      if mod?
      then return ⟨done,l1,l2⟩
      else return ⟨.cons newV newK done,l1,l2⟩
    | .cons v k more => do
        if k == newK
        then
          let ⟨v,l1,l2⟩ ←  mod v l1 l2
          go l1 l2 true (.cons v k done) more
        else
          go l1 l2 true (.cons v k done) more
  go l1 l2 false .nil L


@[specialize]
def ListProd.modifyAddGSpeG
  (l1 : LocalContext) (l2 : LocalInstances)
  {Val Key : Type _} [BEq Key] (L : ListProd Val Key)
  (mod : Val → Key → LocalContext → LocalInstances → MetaM (Prod4 Val Key LocalContext LocalInstances))
  (newK : Key) (final : MetaM (Prod3 (ListProd Val Key) LocalContext LocalInstances))
  : MetaM (Prod3 (ListProd Val Key) LocalContext LocalInstances) :=
  let rec @[specialize] go (l1 : LocalContext) (l2 : LocalInstances) (mod? : Bool) (done : ListProd Val Key)
  : ListProd Val Key → MetaM (Prod3 (ListProd Val Key) LocalContext LocalInstances)
    | .nil =>
      if mod?
      then return ⟨done,l1,l2⟩
      else
        final
    | .cons v k more => do
        if k == newK
        then
          let ⟨v,k,l1,l2⟩ ←  mod v k l1 l2
          go l1 l2 true (.cons v k done) more
        else
          go l1 l2 true (.cons v k done) more
  go l1 l2 false .nil L


@[specialize]
def ListProd.insert_PaInG_proj
  (l1 : LocalContext) (l2 : LocalInstances)
  (singleton : Nat → IdxCollType) (insert : Nat → IdxCollType → IdxCollType)
  (L : CTrie (ListProd IdxCollType (Nat × PaInG IdxCollType)))
  (skipP : Bool) (newN : Name) (newI : Nat) (newE : Expr) (idx : Nat) (depth : Nat)
  (pinsert : Bool → Nat → Expr → Nat → PaInG IdxCollType → LocalContext → LocalInstances → MetaM (Prod3 (PaInG IdxCollType) LocalContext  LocalInstances))
  : MetaM (Prod3 (CTrie (ListProd IdxCollType (Nat × PaInG IdxCollType))) LocalContext  LocalInstances) :=
    L.upsertL l1 l2 newN.toString.toUTF8 (fun
      | .none, l1, l2 => do
          let ⟨res,l1,l2⟩ ← pinsert skipP depth newE idx .dead l1 l2
          return ⟨.some (.cons (singleton idx) (newI, res) .nil),l1,l2⟩
      | .some E, l1, l2 => do
          let ⟨res,l1,l2⟩  ← @ListProd.modifyAddGSpeG l1 l2 IdxCollType (Nat × PaInG IdxCollType)
            ⟨fun x y => x.1 == y.1⟩ E
            (fun x y l1 l2 => do
              let ⟨res,l1,l2⟩ ← pinsert skipP depth newE idx y.2 l1 l2
              return ⟨(insert idx x), (y.1, res),l1,l2⟩
              )
            (newI, PaInG.dead)
            (do
              let ⟨res,l1,l2⟩ ← pinsert skipP depth newE idx .dead l1 l2
              return ⟨(.cons (singleton idx) (newI, res) .nil),l1,l2⟩)
          return ⟨.some res,l1,l2⟩
      )

@[specialize]
def ListProd.insert_PaInG_proj_multi
  (l1 : LocalContext) (l2 : LocalInstances)
  (insert : IdxCollType → IdxCollType → IdxCollType)
  (L : CTrie (ListProd IdxCollType (Nat × PaInG IdxCollType)))
  (skipP : Bool) (newN : Name) (newI : Nat) (newE : Expr) (idx : IdxCollType) (depth : Nat)
  (pinsert : Bool → Nat → Expr → IdxCollType → PaInG IdxCollType → LocalContext → LocalInstances → MetaM (Prod3 (PaInG IdxCollType) LocalContext  LocalInstances))
  : MetaM (Prod3 (CTrie (ListProd IdxCollType (Nat × PaInG IdxCollType))) LocalContext  LocalInstances) :=
    L.upsertL l1 l2 newN.toString.toUTF8 (fun
      | .none, l1, l2 => do
          let ⟨res,l1,l2⟩ ← pinsert skipP depth newE idx .dead l1 l2
          return ⟨.some (.cons idx (newI, res) .nil),l1,l2⟩
      | .some E, l1, l2 => do
          let ⟨res,l1,l2⟩  ← @ListProd.modifyAddGSpeG l1 l2 IdxCollType (Nat × PaInG IdxCollType)
            ⟨fun x y => x.1 == y.1⟩ E
            (fun x y l1 l2 => do
              let ⟨res,l1,l2⟩ ← pinsert skipP depth newE idx y.2 l1 l2
              return ⟨(insert idx x), (y.1, res),l1,l2⟩
              )
            (newI, PaInG.dead)
            (do
              let ⟨res,l1,l2⟩ ← pinsert skipP depth newE idx .dead l1 l2
              return ⟨(.cons idx (newI, res) .nil),l1,l2⟩)
          return ⟨.some res,l1,l2⟩
      )
