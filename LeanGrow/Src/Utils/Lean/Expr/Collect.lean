
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Lean.Expr
import LeanGrow.Src.Utils.Tracing
import LeanGrow.Src.Utils.Lean.LocalContext
import LeanGrow.Src.Utils.LeanGrow.Nodes

open Lean Meta



@[specialize f, inline]
partial def Lean.Expr.onAllSubtermsCheckExistsTR (e : Expr) (f : Expr → Bool) : Bool :=
  let rec @[specialize f] go : List Expr → Bool
    | [] => false
    | e :: more =>
      if f e
      then true
      else
        match e with
        | .app l r => go (l :: r :: more)
        | .lam _ l r _ => go (l :: r :: more)
        | .forallE _ l r _ => go (l :: r :: more)
        | .letE _ l r z _ => go (l :: r :: z :: more)
        | .proj _ _ e => go (e :: more)
        | .mdata _ e => go (e :: more)
        | _ => go more
  go [e]

@[specialize f, inline]
partial def Lean.Expr.onAllSubtermsCheckExists (e : Expr) (f : Expr → Bool) : Bool :=
  let rec @[specialize f] go : Expr → Bool
    | e  =>
      if f e
      then true
      else
        match e with
        | .app l r => if go l then true else go r
        | .lam _ l r _ => if go l then true else go r
        | .forallE _ l r _ => if go l then true else go r
        | .letE _ l r z _ => if go l then true else (if go r then true else go z)
        | .proj _ _ e | .mdata _ e => go e
        | _ => false
  go e

@[specialize f, inline]
partial def Lean.Expr.onAllSubtermsCheckExistsSkipTR (e : Expr) (f : Expr → (Bool × Bool)) : Bool :=
  let rec @[specialize f] go : List Expr → Bool
    | [] => false
    | e :: more =>
      let (pat,skip) := f e
      if pat
      then true
      else
        if skip
        then go more
        else
          match e with
          | .app l r => go (l :: r :: more)
          | .lam _ l r _ => go (l :: r :: more)
          | .forallE _ l r _ => go (l :: r :: more)
          | .letE _ l r z _ => go (l :: r :: z :: more)
          | .proj _ _ e => go (e :: more)
          | .mdata _ e => go (e :: more)
          | _ => go more
  go [e]


@[specialize f, inline]
partial def Lean.Expr.onAllSubtermsCheckExistsSkip (e : Expr) (f : Expr → (Bool × Bool)) : Bool :=
  let rec @[specialize f] go : Expr → Bool
    | e  =>
      let (pat,skip) := f e
      if pat
      then true
      else
        if skip
        then false
        else
          match e with
          | .app l r => if go l then true else go r
          | .lam _ l r _ => if go l then true else go r
          | .forallE _ l r _ => if go l then true else go r
          | .letE _ l r z _ => if go l then true else (if go r then true else go z)
          | .proj _ _ e | .mdata _ e => go e
          | _ => false
  go e


@[specialize f, inline]
partial def Lean.Expr.onAllSubtermsgetFirstTR (e : Expr) {α : Sort _} (f : Expr → Option α) : Option α :=
  let rec @[specialize f] go : List Expr → Option α
    | [] => .none
    | e :: more =>
      match f e with
      | res@(.some ..) => res
      | .none =>
          match e with
          | .app l r => go (l :: r :: more)
          | .lam _ l r _ => go (l :: r :: more)
          | .forallE _ l r _ => go (l :: r :: more)
          | .letE _ l r z _ => go (l :: r :: z :: more)
          | .proj _ _ e => go (e :: more)
          | .mdata _ e => go (e :: more)
          | _ => go more
  go [e]

@[specialize f, inline]
partial def Lean.Expr.onAllSubtermsgetFirst (e : Expr) {α : Sort _} (f : Expr → Option α) : Option α :=
  let rec @[specialize f] go : Expr → Option α
    | e =>
      match f e with
      | res@(.some ..) => res
      | .none =>
          match e with
          | .app l r => (match go l with | R@(.some ..) => R | _ => go r)
          | .lam _ l r _ => (match go l with | R@(.some ..) => R | _ => go r)
          | .forallE _ l r _ => (match go l with | R@(.some ..) => R | _ => go r)
          | .letE _ l r z _ => (match go l with | R@(.some ..) => R | _ => (match go r with | R@(.some ..) => R | _ => go z))
          | .proj _ _ e | .mdata _ e => go e
          | _ => .none
  go e


inductive ListProdSpe1 (α β : Sort _) where
  | nil | cons (a : α) (b : β) (nx : ListProdSpe1 α β) | sig (n : Nat) (nx : ListProdSpe1 α β)


@[specialize f, inline]
partial def Lean.Expr.onAllSubtermsCheckExistsMTR (e : Expr) (initD : LocalContext) (initI : LocalInstances)
  (f : Expr → Nat → LocalContext → LocalInstances → MetaM (Prod3 Bool LocalContext LocalInstances))
  : MetaM (Prod3 Bool LocalContext LocalInstances) :=
  let rec @[specialize f] go (initD : LocalContext) (initI : LocalInstances) : ListProdSpe1 Nat Expr → MetaM (Prod3 Bool LocalContext LocalInstances)
    | .nil => return ⟨false, initD, initI⟩
    | .sig binfo more =>
      go initD (initI.patch binfo 1) more
    | .cons d e more => do
      let ⟨cond, initD, initI⟩ ← f e d initD initI
      if cond
      then return ⟨true, initD, initI⟩
      else
        match e with
        | .app l r => go initD initI (.cons d l <| .cons d r more)
        | .lam _ l r _ =>
            let S := initI.size
            let fv ← worker d
            let ⟨_,r,initD,initI⟩ ← withFreeing fv l r initD initI
            go initD initI (.cons d l <| .cons (d+1) r <| .sig S more)
        | .forallE _ l r _ =>
            let S := initI.size
            let fv ← worker d
            let ⟨_,r,initD,initI⟩ ← withFreeing fv l r initD initI
            go initD initI (.cons d l <| .cons (d+1) r <| .sig S more)
        | .letE _ l r z _ =>
            let S := initI.size
            let fv ← worker d
            let ⟨_,z,initD,initI⟩ ← withFreeingLet fv l r z initD initI
            go initD initI (.cons d l <| .cons d r <| .cons (d+1) z <| .sig S more)
        | .proj _ _ e => go initD initI (.cons d e more)
        | .mdata _ e => go initD initI (.cons d e more)
        | _ => go initD initI more
  go initD initI <| .cons 0 e .nil




@[specialize f, inline]
partial def Lean.Expr.onAllSubtermsCheckExistsM (e : Expr) (l1 : LocalContext) (l2 : LocalInstances)
  (f : Expr → Nat → LocalContext → LocalInstances → MetaM (Prod3 Bool LocalContext LocalInstances))
  : MetaM (Prod3 Bool LocalContext LocalInstances) :=
  let rec @[specialize f] go (d : Nat) (l1 : LocalContext) (l2 : LocalInstances) : Expr → MetaM (Prod3 Bool LocalContext LocalInstances)
    | e  => do
      let R@⟨here,l1,l2⟩ ← f e d l1 l2
      if here
      then return R
      else
        match e with
        | .app l r =>
            let R@⟨here,l1,l2⟩ ← go d l1 l2 l
            if here then return R else go d l1 l2 r
        | .lam _ l r _ =>
            let R@⟨here,l1,l2⟩ ← go d l1 l2 l
            if here
            then return R
            else
              let S := l2.size
              let fv ← worker d
              let ⟨_,r,l1,l2⟩ ← withFreeing fv l r l1 l2
              let ⟨here,l1,l2⟩ ← go d l1 l2 r
              let l2 := l2.patch S 1
              return ⟨here,l1,l2⟩
        | .forallE _ l r _ =>
            let R@⟨here,l1,l2⟩ ← go d l1 l2 l
            if here
            then return R
            else
              let S := l2.size
              let fv ← worker d
              let ⟨_,r,l1,l2⟩ ← withFreeing fv l r l1 l2
              let ⟨here,l1,l2⟩ ← go d l1 l2 r
              let l2 := l2.patch S 1
              return ⟨here,l1,l2⟩
        | .letE _ l r z _ =>
            let R@⟨here,l1,l2⟩ ← go d l1 l2 l
            if here
            then return R
            else
              let R@⟨here,l1,l2⟩ ← go d l1 l2 r
              if here
              then return R
              else
                let S := l2.size
                let fv ← worker d
                let ⟨_,z,l1,l2⟩ ← withFreeingLet fv l r z l1 l2
                let ⟨here,l1,l2⟩ ← go d l1 l2 z
                let l2 := l2.patch S 1
                return ⟨here,l1,l2⟩
        | .proj _ _ e | .mdata _ e => go d l1 l2 e
        | _ => return ⟨false,l1,l2⟩
  go 0 l1 l2 e

@[specialize f, inline]
partial def Lean.Expr.onAllSubtermsCheckExistsTrackedMTR (e : Expr) (initD : LocalContext) (initI : LocalInstances)
  (f : Expr → Nat → Array Expr → LocalContext → LocalInstances → MetaM (Prod3 Bool LocalContext LocalInstances))
  : MetaM (Prod3 Bool LocalContext LocalInstances) :=
  let rec @[specialize f] go (workas : Array Expr) (initD : LocalContext) (initI : LocalInstances) : ListProdSpe1 Nat Expr → MetaM (Prod3 Bool LocalContext LocalInstances)
    | .nil => return ⟨false, initD, initI⟩
    | .sig binfo more =>
      go workas initD (initI.patch binfo 1) more
    | .cons d e more => do
      let ⟨cond, initD, initI⟩ ← f e d workas initD initI
      if cond
      then return ⟨true, initD, initI⟩
      else
        match e with
        | .app l r => go workas initD initI (.cons d l <| .cons d r more)
        | .lam _ l r _ =>
            let S := initI.size
            let fv ← worker d
            let ⟨fv,r,initD,initI⟩ ← withFreeing fv l r initD initI
            go (workas.push (.fvar fv)) initD initI (.cons d l <| .cons (d+1) r <| .sig S more)
        | .forallE _ l r _ =>
            let S := initI.size
            let fv ← worker d
            let ⟨fv,r,initD,initI⟩ ← withFreeing fv l r initD initI
            go (workas.push (.fvar fv)) initD initI (.cons d l <| .cons (d+1) r <| .sig S more)
        | .letE _ l r z _ =>
            let S := initI.size
            let fv ← worker d
            let ⟨fv,z,initD,initI⟩ ← withFreeingLet fv l r z initD initI
            go (workas.push (.fvar fv)) initD initI (.cons d l <| .cons d r <| .cons (d+1) z <| .sig S more)
        | .proj _ _ e => go workas initD initI (.cons d e more)
        | .mdata _ e => go workas initD initI (.cons d e more)
        | _ => go workas initD initI more
  go #[] initD initI <| .cons 0 e .nil



@[specialize f, inline]
partial def Lean.Expr.onAllSubtermsCheckExistsTrackedM (e : Expr) (l1 : LocalContext) (l2 : LocalInstances)
  (f : Expr → Nat → Array Expr → LocalContext → LocalInstances → MetaM (Prod3 Bool LocalContext LocalInstances))
  : MetaM (Prod3 Bool LocalContext LocalInstances) :=
  let rec @[specialize f] go (workas : Array Expr) (d : Nat) (l1 : LocalContext) (l2 : LocalInstances) : Expr → MetaM (Prod3 Bool LocalContext LocalInstances)
    -- Debt : `workas` should be passed as state for linear use ...
    | e  => do
      let R@⟨here,l1,l2⟩ ← f e d workas l1 l2
      if here
      then return R
      else
        match e with
        | .app l r =>
            let R@⟨here,l1,l2⟩ ← go workas d l1 l2 l
            if here then return R else go workas d l1 l2 r
        | .lam _ l r _ =>
            let R@⟨here,l1,l2⟩ ← go workas d l1 l2 l
            if here
            then return R
            else
              let S := l2.size
              let fv ← worker d
              let ⟨fv,r,l1,l2⟩ ← withFreeing fv l r l1 l2
              let ⟨here,l1,l2⟩ ← go (workas.push (.fvar fv)) d l1 l2 r
              let l2 := l2.patch S 1
              return ⟨here,l1,l2⟩
        | .forallE _ l r _ =>
            let R@⟨here,l1,l2⟩ ← go workas d l1 l2 l
            if here
            then return R
            else
              let S := l2.size
              let fv ← worker d
              let ⟨fv,r,l1,l2⟩ ← withFreeing fv l r l1 l2
              let ⟨here,l1,l2⟩ ← go (workas.push (.fvar fv)) d l1 l2 r
              let l2 := l2.patch S 1
              return ⟨here,l1,l2⟩
        | .letE _ l r z _ =>
            let R@⟨here,l1,l2⟩ ← go workas d l1 l2 l
            if here
            then return R
            else
              let R@⟨here,l1,l2⟩ ← go workas d l1 l2 r
              if here
              then return R
              else
                let S := l2.size
                let fv ← worker d
                let ⟨fv,z,l1,l2⟩ ← withFreeingLet fv l r z l1 l2
                let ⟨here,l1,l2⟩ ← go (workas.push (.fvar fv)) d l1 l2 z
                let l2 := l2.patch S 1
                return ⟨here,l1,l2⟩
        | .proj _ _ e | .mdata _ e => go workas d l1 l2 e
        | _ => return ⟨false,l1,l2⟩
  go #[] 0 l1 l2 e





@[specialize, inline]
partial def Lean.Expr.onAllSubtermsFoldMTR (e : Expr) (initD : LocalContext) (initI : LocalInstances)
  {α : Sort _} (initA : α)
  (f : Expr → Nat → Array Expr → LocalContext → LocalInstances → α → MetaM (Prod3 α LocalContext LocalInstances))
  : MetaM (Prod3 α LocalContext LocalInstances) :=
  let rec @[specialize] go (workas : Array Expr) (initD : LocalContext) (initI : LocalInstances) (col : α)
    : ListProdSpe1 Nat Expr → MetaM (Prod3 α LocalContext LocalInstances)
    | .nil => return ⟨col,initD,initI⟩
    | .sig binfo more =>
      go workas initD (initI.patch binfo 1) col more
    | .cons d e more => do
      let ⟨col,initD,initI⟩ ← f e d workas initD initI col
      match e with
      | .app l r => go workas initD initI col (.cons d l <| .cons d r more)
      | .lam _ l r _ =>
          let S := initI.size
          let fv ← worker d
          let ⟨fv,r,initD,initI⟩ ← withFreeing fv l r initD initI
          go (workas.push (.fvar fv)) initD initI col (.cons d l <| .cons (d+1) r <| .sig S more)
      | .forallE _ l r _ =>
          let S := initI.size
          let fv ← worker d
          let ⟨fv,r,initD,initI⟩ ← withFreeing fv l r initD initI
          go (workas.push (.fvar fv)) initD initI col (.cons d l <| .cons (d+1) r <| .sig S more)
      | .letE _ l r z _ =>
          let S := initI.size
          let fv ← worker d
          let ⟨fv,z,initD,initI⟩ ← withFreeingLet fv l r z initD initI
          go (workas.push (.fvar fv)) initD initI col (.cons d l <| .cons d r <| .cons (d+1) z <| .sig S more)
      | .proj _ _ e => go workas initD initI col (.cons d e more)
      | .mdata _ e => go workas initD initI col (.cons d e more)
      | _ => go workas initD initI col more
  go {} initD initI initA <| .cons 0 e .nil


@[specialize, inline]
partial def Lean.Expr.onAllSubtermsFoldM (e : Expr) (l1 : LocalContext) (l2 : LocalInstances)
  {α : Sort _} (initA : α)
  (f : Expr → Nat → Array Expr → LocalContext → LocalInstances → α → MetaM (Prod3 α LocalContext LocalInstances))
  : MetaM (Prod3 α LocalContext LocalInstances) :=
  let rec @[specialize] go (d : Nat) (workas : Array Expr) (l1 : LocalContext) (l2 : LocalInstances) (col : α)
    (e : Expr) : MetaM (Prod3 α LocalContext LocalInstances) := do
      let ⟨col,initD,initI⟩ ← f e d workas l1 l2 col
      match e with
      | .app l r =>
          let ⟨col,initD,initI⟩ ← go d workas initD initI col l
          go d workas initD initI col r
      | .lam _ l r _ | .forallE _ l r _ =>
          let ⟨col,initD,initI⟩ ← go d workas initD initI col l
          let S := initI.size
          let fv ← worker d
          let ⟨fv,r,initD,initI⟩ ← withFreeing fv l r initD initI
          let ⟨col,initD,initI⟩ ← go (d+1) (workas.push (.fvar fv)) initD initI col r
          let initI := initI.patch S 1
          return ⟨col,initD,initI⟩
      | .letE _ l r z _ =>
          let ⟨col,initD,initI⟩ ← go d workas initD initI col l
          let ⟨col,initD,initI⟩ ← go d workas initD initI col r
          let S := initI.size
          let fv ← worker d
          let ⟨fv,z,initD,initI⟩ ← withFreeingLet fv l r z initD initI
          let ⟨col,initD,initI⟩ ← go (d+1) (workas.push (.fvar fv)) initD initI col z
          let initI := initI.patch S 1
          return ⟨col,initD,initI⟩
      | .proj _ _ e => go d workas initD initI col e
      | .mdata _ e => go d workas initD initI col e
      | _ => return ⟨col,initD,initI⟩
  go 0 #[] l1 l2 initA e


@[specialize, inline]
partial def Lean.Expr.onAllSubtermsFoldSkipMTR (e : Expr) (initD : LocalContext) (initI : LocalInstances)
  {α : Sort _} (initA : α)
  (f : Expr → Nat → Array Expr → LocalContext → LocalInstances → α → MetaM (Prod4 α Bool LocalContext LocalInstances))
  : MetaM (Prod3 α LocalContext LocalInstances) :=
  let rec @[specialize] go (workas : Array Expr) (initD : LocalContext) (initI : LocalInstances) (col : α)
    : ListProdSpe1 Nat Expr → MetaM (Prod3 α LocalContext LocalInstances)
    | .nil => return ⟨col,initD,initI⟩
    | .sig binfo more =>
      go workas initD (initI.patch binfo 1) col more
    | .cons d e more => do
      let ⟨col,skip,initD,initI⟩ ← f e d workas initD initI col
      if skip
      then go workas initD initI col more
      else
        match e with
        | .app l r => go workas initD initI col (.cons d l <| .cons d r more)
        | .lam _ l r _ =>
            let S := initI.size
            let fv ← worker d
            let ⟨fv,r,initD,initI⟩ ← withFreeing fv l r initD initI
            go (workas.push (.fvar fv)) initD initI col (.cons d l <| .cons (d+1) r <| .sig S more)
        | .forallE _ l r _ =>
            let S := initI.size
            let fv ← worker d
            let ⟨fv,r,initD,initI⟩ ← withFreeing fv l r initD initI
            go (workas.push (.fvar fv)) initD initI col (.cons d l <| .cons (d+1) r <| .sig S more)
        | .letE _ l r z _ =>
            let S := initI.size
            let fv ← worker d
            let ⟨fv,z,initD,initI⟩ ← withFreeingLet fv l r z initD initI
            go (workas.push (.fvar fv)) initD initI col (.cons d l <| .cons d r <| .cons (d+1) z <| .sig S more)
        | .proj _ _ e => go workas initD initI col (.cons d e more)
        | .mdata _ e => go workas initD initI col (.cons d e more)
        | _ => go workas initD initI col more
  go {} initD initI initA <| .cons 0 e .nil


@[specialize, inline]
partial def Lean.Expr.onAllSubtermsFoldSkipM (e : Expr) (l1 : LocalContext) (l2 : LocalInstances)
  {α : Sort _} (initA : α)
  (f : Expr → Nat → Array Expr → LocalContext → LocalInstances → α → MetaM (Prod4 α Bool LocalContext LocalInstances))
  : MetaM (Prod3 α LocalContext LocalInstances) :=
  let rec @[specialize] go (d : Nat) (workas : Array Expr) (l1 : LocalContext) (l2 : LocalInstances) (col : α)
    (e : Expr) : MetaM (Prod3 α LocalContext LocalInstances) := do
      let ⟨col,skip,initD,initI⟩ ← f e d workas l1 l2 col
      if skip
      then return ⟨col,initD,initI⟩
      else
        match e with
        | .app l r =>
            let ⟨col,initD,initI⟩ ← go d workas initD initI col l
            go d workas initD initI col r
        | .lam _ l r _ | .forallE _ l r _ =>
            let ⟨col,initD,initI⟩ ← go d workas initD initI col l
            let S := initI.size
            let fv ← worker d
            let ⟨fv,r,initD,initI⟩ ← withFreeing fv l r initD initI
            let ⟨col,initD,initI⟩ ← go (d+1) (workas.push (.fvar fv)) initD initI col r
            let initI := initI.patch S 1
            return ⟨col,initD,initI⟩
        | .letE _ l r z _ =>
            let ⟨col,initD,initI⟩ ← go d workas initD initI col l
            let ⟨col,initD,initI⟩ ← go d workas initD initI col r
            let S := initI.size
            let fv ← worker d
            let ⟨fv,z,initD,initI⟩ ← withFreeingLet fv l r z initD initI
            let ⟨col,initD,initI⟩ ← go (d+1) (workas.push (.fvar fv)) initD initI col z
            let initI := initI.patch S 1
            return ⟨col,initD,initI⟩
        | .proj _ _ e => go d workas initD initI col e
        | .mdata _ e => go d workas initD initI col e
        | _ => return ⟨col,initD,initI⟩
  go 0 #[] l1 l2 initA e



@[specialize f, inline]
partial def Lean.Expr.onAllSubtermsFoldTR (e : Expr)
  {α : Sort _} (init : α) (f : Expr → α → α) : α :=
  let rec @[specialize f] go (col : α) : List Expr → α
    | [] => col
    | e :: more =>
      let here := f e col
      match e with
      | .app l r => go (here) (l :: r :: more)
      | .lam _ l r _ => go (here) (l :: r :: more)
      | .forallE _ l r _ => go (here)  (l :: r :: more)
      | .letE _ l r z _ => go (here)  (l :: r :: z :: more)
      | .proj _ _ e => go (here)  (e :: more)
      | .mdata _ e => go (here) (e :: more)
      | _ => go (here) more
  go init [e]


@[specialize f, inline]
partial def Lean.Expr.onAllSubtermsFold (e : Expr)
  {α : Sort _} (init : α) (f : Expr → α → α) : α :=
  let rec @[specialize f] go (col : α) : Expr → α
    | e =>
      let here := f e col
      match e with
      | .app l r | .lam _ l r _ | .forallE _ l r _ => go (go here l) r
      | .letE _ l r z _ => go (go (go here l) r) z
      | .proj _ _ e => go (here) e
      | .mdata _ e => go (here) e
      | _ => here
  go init e


@[specialize f, inline]
partial def Lean.Expr.onAllSubtermsFoldSkipTR (e : Expr)
  {α : Sort _} (init : α) (f : Expr → α → α × Bool) : α :=
  let rec @[specialize f] go (col : α) : List Expr → α
    | [] => col
    | e :: more =>
      let (here,skip?) := f e col
      if skip?
      then go here more
      else
        match e with
        | .app l r => go (here) (l :: r :: more)
        | .lam _ l r _ => go (here) (l :: r :: more)
        | .forallE _ l r _ => go (here)  (l :: r :: more)
        | .letE _ l r z _ => go (here)  (l :: r :: z :: more)
        | .proj _ _ e => go (here)  (e :: more)
        | .mdata _ e => go (here) (e :: more)
        | _ => go (here) more
  go init [e]


@[specialize f, inline]
partial def Lean.Expr.onAllSubtermsFoldSkip (e : Expr)
  {α : Sort _} (init : α) (f : Expr → α → α × Bool) : α :=
  let rec @[specialize f] go (col : α) : Expr → α
    | e =>
      let (here,skip?) := f e col
      if skip?
      then here
      else
        match e with
        | .app l r | .lam _ l r _ | .forallE _ l r _ => go (go here l) r
        | .letE _ l r z _ => go (go (go here l) r) z
        | .proj _ _ e => go (here) e
        | .mdata _ e => go (here) e
        | _ => here
  go init e


inductive FoldEnqueueT (α : Sort _) where
| std (a : α)
| enq (a : α) (depth : Nat) (enq : Expr)
deriving Inhabited

@[specialize, inline]
partial def Lean.Expr.onAllSubtermsFoldEnqueueM (e : Expr) (initD : LocalContext) (initI : LocalInstances)
  {α : Sort _} (initA : α)
  (f : Expr → Nat → Array Expr → LocalContext → LocalInstances → α → MetaM (Prod3 (FoldEnqueueT α) LocalContext LocalInstances))
  : MetaM (Prod3 α LocalContext LocalInstances) :=
  let rec @[specialize] go (workas : Array Expr) (initD : LocalContext) (initI : LocalInstances) (col : α)
    : ListProdSpe1 Nat Expr → MetaM (Prod3 α LocalContext LocalInstances)
    | .nil => return ⟨col,initD,initI⟩
    | .sig binfo more =>
      go workas initD (initI.patch binfo 1) col more
    | .cons d e more => do
      let ⟨pack,initD,initI⟩  ← f e d workas initD initI col
      match pack with
      | .std col =>
          match e with
          | .app l r => go workas initD initI col (.cons d l <| .cons d r more)
          | .lam _ l r _ =>
              let S := initI.size
              let fv ← worker d
              let ⟨fv,r,initD,initI⟩ ← withFreeing fv l r initD initI
              go (workas.push (.fvar fv)) initD initI col (.cons d l <| .cons (d+1) r <| .sig S more)
          | .forallE _ l r _ =>
              let S := initI.size
              let fv ← worker d
              let ⟨fv,r,initD,initI⟩ ← withFreeing fv l r initD initI
              go (workas.push (.fvar fv)) initD initI col (.cons d l <| .cons (d+1) r <| .sig S more)
          | .letE _ l r z _ =>
              let S := initI.size
              let fv ← worker d
              let ⟨fv,z,initD,initI⟩ ← withFreeingLet fv l r z initD initI
              go (workas.push (.fvar fv)) initD initI col (.cons d l <| .cons d r <| .cons (d+1) z <| .sig S more)
          | .proj _ _ e => go workas initD initI col (.cons d e more)
          | .mdata _ e => go workas initD initI col (.cons d e more)
          | _ => go workas initD initI col more
      | .enq col enqD enq =>
          match e with
          | .app l r => go workas initD initI col (.cons enqD enq <| .cons d l <| .cons d r more)
          | .lam _ l r _ =>
              let S := initI.size
              let fv ← worker d
              let ⟨fv,r,initD,initI⟩ ← withFreeing fv l r initD initI
              go (workas.push (.fvar fv)) initD initI col (.cons enqD enq <| .cons d l <| .cons (d+1) r <| .sig S more)
          | .forallE _ l r _ =>
              let S := initI.size
              let fv ← worker d
              let ⟨fv,r,initD,initI⟩ ← withFreeing fv l r initD initI
              go (workas.push (.fvar fv)) initD initI col (.cons enqD enq <| .cons d l <| .cons (d+1) r <| .sig S more)
          | .letE _ l r z _ =>
              let S := initI.size
              let fv ← worker d
              let ⟨fv,z,initD,initI⟩ ← withFreeingLet fv l r z initD initI
              go (workas.push (.fvar fv)) initD initI col (.cons enqD enq <| .cons d l <| .cons d r <| .cons (d+1) z <| .sig S more)
          | .proj _ _ e => go workas initD initI col (.cons enqD enq <| .cons d e more)
          | .mdata _ e => go workas initD initI col (.cons enqD enq <| .cons d e more)
          | _ => go workas initD initI col (.cons enqD enq more)
  go {} initD initI initA <| .cons 0 e .nil

@[specialize f, inline]
partial def Lean.Expr.onAllSubtermsFoldNoPartialM (e : Expr) (initD : LocalContext) (initI : LocalInstances)
  {α : Sort _} (init : α) (f : Expr → Nat → Array Expr → α → LocalContext → LocalInstances → MetaM (Prod3 α LocalContext LocalInstances))
  : MetaM (Prod3 α LocalContext LocalInstances) :=
  let rec getApp (d : Nat) (as : ListProdSpe1 Nat Expr) : Expr → ListProdSpe1 Nat Expr
    | .app l r => getApp d (.cons d r as) l
    | h => .cons d h as
  let rec @[specialize f] go (workas : Array Expr) (initD : LocalContext) (initI : LocalInstances) (col : α)
    : ListProdSpe1 Nat Expr → MetaM (Prod3 α LocalContext LocalInstances)
    | .nil => return ⟨col,initD,initI⟩
    | .sig binfo more =>
      go workas initD (initI.patch binfo 1) col more
    | .cons d e more => do
        let ⟨here,initD,initI⟩  ← f e d workas col initD initI
        match e with
        | .app .. =>
            go workas initD initI (here) (getApp d more e)
        | .lam _ l r _ =>
            let S := initI.size
            let fv ← worker d
            let ⟨fv,r,initD,initI⟩ ← withFreeing fv l r initD initI
            go (workas.push (.fvar fv)) initD initI (here) (.cons d l <| .cons (d+1) r <| .sig S more)
        | .forallE _ l r _ =>
            let S := initI.size
            let fv ← worker d
            let ⟨fv,r,initD,initI⟩ ← withFreeing fv l r initD initI
            go (workas.push (.fvar fv)) initD initI (here) (.cons d l <| .cons (d+1) r <| .sig S more)
        | .letE _ l r z _ =>
            let S := initI.size
            let fv ← worker d
            let ⟨fv,z,initD,initI⟩ ← withFreeingLet fv l r z initD initI
            go (workas.push (.fvar fv)) initD initI (here) (.cons d l <| .cons d r <| .cons (d+1) z <| .sig S more)
        | .proj _ _ e => go workas initD initI (here) (.cons d e more)
        | .mdata _ e => go workas initD initI (here) (.cons d e more)
        | _ => go workas initD initI (here) more
  go {} initD initI init <| .cons 0 e .nil
