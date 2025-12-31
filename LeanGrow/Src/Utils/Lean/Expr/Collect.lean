
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Lean.Expr
import LeanGrowBeta.Utils.Tracing
import LeanGrowBeta.Utils.Lean.LocalContext
import LeanGrowBeta.Utils.LeanGrow.Nodes
import LeanGrowBeta.Data.CTrie.Basic

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
partial def Lean.Expr.onAllSubtermsgetFirst (e : Expr) {α : Sort _} (f : Expr → Option α) : Option α :=
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
partial def Lean.Expr.onAllSubtermsCheckExistsMTR (e : Expr) (initD : LocalContext) (initI : LocalInstances)
  (f : Expr → Nat → LocalContext → LocalInstances → MetaM (Prod3 Bool LocalContext LocalInstances))
  : MetaM (Prod3 Bool LocalContext LocalInstances) :=
  let rec @[specialize f] go (initD : LocalContext) (initI : LocalInstances) : ListProd Nat Expr → MetaM (Prod3 Bool LocalContext LocalInstances)
    | .nil => return ⟨false, initD, initI⟩
    | .cons d e more => do
      let ⟨cond, initD, initI⟩ ← f e d initD initI
      if cond
      then return ⟨true, initD, initI⟩
      else
        match e with
        | .app l r => go initD initI (.cons d l <| .cons d r more)
        | .lam _ l r _ =>
            let fv ← worker d
            let ⟨_,r,initD,initI⟩ ← withFreeing fv l r initD initI
            go initD initI (.cons d l <| .cons (d+1) r more)
        | .forallE _ l r _ =>
            let fv ← worker d
            let ⟨_,r,initD,initI⟩ ← withFreeing fv l r initD initI
            go initD initI (.cons d l <| .cons (d+1) r more)
        | .letE _ l r z _ =>
            let fv ← worker d
            let ⟨_,z,initD,initI⟩ ← withFreeingLet fv l r z initD initI
            go initD initI (.cons d l <| .cons d r <| .cons (d+1) z more)
        | .proj _ _ e => go initD initI (.cons d e more)
        | .mdata _ e => go initD initI (.cons d e more)
        | _ => go initD initI more
  go initD initI <| .cons 0 e .nil

@[specialize f, inline]
partial def Lean.Expr.onAllSubtermsCheckExistsTrackedMTR (e : Expr) (initD : LocalContext) (initI : LocalInstances)
  (f : Expr → Nat → CTrie Unit → LocalContext → LocalInstances → MetaM (Prod3 Bool LocalContext LocalInstances))
  : MetaM (Prod3 Bool LocalContext LocalInstances) :=
  let rec @[specialize f] go (workas : CTrie Unit) (initD : LocalContext) (initI : LocalInstances) : ListProd Nat Expr → MetaM (Prod3 Bool LocalContext LocalInstances)
    | .nil => return ⟨false, initD, initI⟩
    | .cons d e more => do
      let ⟨cond, initD, initI⟩ ← f e d workas initD initI
      if cond
      then return ⟨true, initD, initI⟩
      else
        match e with
        | .app l r => go workas initD initI (.cons d l <| .cons d r more)
        | .lam _ l r _ =>
            let fv ← worker d
            let workas := workas.insert fv.toString.toUTF8 ()
            let ⟨_,r,initD,initI⟩ ← withFreeing fv l r initD initI
            go workas initD initI (.cons d l <| .cons (d+1) r more)
        | .forallE _ l r _ =>
            let fv ← worker d
            let workas := workas.insert fv.toString.toUTF8 ()
            let ⟨_,r,initD,initI⟩ ← withFreeing fv l r initD initI
            go workas initD initI (.cons d l <| .cons (d+1) r more)
        | .letE _ l r z _ =>
            let fv ← worker d
            let workas := workas.insert fv.toString.toUTF8 ()
            let ⟨_,z,initD,initI⟩ ← withFreeingLet fv l r z initD initI
            go workas initD initI (.cons d l <| .cons d r <| .cons (d+1) z more)
        | .proj _ _ e => go workas initD initI (.cons d e more)
        | .mdata _ e => go workas initD initI (.cons d e more)
        | _ => go workas initD initI more
  go {} initD initI <| .cons 0 e .nil



@[specialize, inline]
partial def Lean.Expr.onAllSubtermsFoldM (e : Expr) (initD : LocalContext) (initI : LocalInstances)
  {α : Sort _} (initA : α)
  (f : Expr → Nat → CTrie Unit → LocalContext → LocalInstances → α → MetaM (Prod3 α LocalContext LocalInstances))
  : MetaM (Prod3 α LocalContext LocalInstances) :=
  let rec @[specialize] go (workas : CTrie Unit) (initD : LocalContext) (initI : LocalInstances) (col : α)
    : ListProd Nat Expr → MetaM (Prod3 α LocalContext LocalInstances)
    | .nil => return ⟨col,initD,initI⟩
    | .cons d e more => do
      let ⟨col,initD,initI⟩  ← f e d workas initD initI col
      match e with
      | .app l r => go workas initD initI col (.cons d l <| .cons d r more)
      | .lam _ l r _ =>
          let fv ← worker d
          let workas := workas.insert fv.toString.toUTF8 ()
          let ⟨_,r,initD,initI⟩ ← withFreeing fv l r initD initI
          go workas initD initI col (.cons d l <| .cons (d+1) r more)
      | .forallE _ l r _ =>
          let fv ← worker d
          let workas := workas.insert fv.toString.toUTF8 ()
          let ⟨_,r,initD,initI⟩ ← withFreeing fv l r initD initI
          go workas initD initI col (.cons d l <| .cons (d+1) r more)
      | .letE _ l r z _ =>
          let fv ← worker d
          let workas := workas.insert fv.toString.toUTF8 ()
          let ⟨_,z,initD,initI⟩ ← withFreeingLet fv l r z initD initI
          go workas initD initI col (.cons d l <| .cons d r <| .cons (d+1) z more)
      | .proj _ _ e => go workas initD initI col (.cons d e more)
      | .mdata _ e => go workas initD initI col (.cons d e more)
      | _ => go workas initD initI col more
  go {} initD initI initA <| .cons 0 e .nil




@[specialize f, inline]
partial def Lean.Expr.onAllSubtermsFold (e : Expr)
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



inductive FoldEnqueueT (α : Sort _) where
| std (a : α)
| enq (a : α) (depth : Nat) (enq : Expr)
deriving Inhabited

@[specialize, inline]
partial def Lean.Expr.onAllSubtermsFoldEnqueueM (e : Expr) (initD : LocalContext) (initI : LocalInstances)
  {α : Sort _} (initA : α)
  (f : Expr → Nat → CTrie Unit → LocalContext → LocalInstances → α → MetaM (Prod3 (FoldEnqueueT α) LocalContext LocalInstances))
  : MetaM (Prod3 α LocalContext LocalInstances) :=
  let rec @[specialize] go (workas : CTrie Unit) (initD : LocalContext) (initI : LocalInstances) (col : α)
    : ListProd Nat Expr → MetaM (Prod3 α LocalContext LocalInstances)
    | .nil => return ⟨col,initD,initI⟩
    | .cons d e more => do
      let ⟨pack,initD,initI⟩  ← f e d workas initD initI col
      match pack with
      | .std col =>
          match e with
          | .app l r => go workas initD initI col (.cons d l <| .cons d r more)
          | .lam _ l r _ =>
              let fv ← worker d
              let workas := workas.insert fv.toString.toUTF8 ()
              let ⟨_,r,initD,initI⟩ ← withFreeing fv l r initD initI
              go workas initD initI col (.cons d l <| .cons (d+1) r more)
          | .forallE _ l r _ =>
              let fv ← worker d
              let workas := workas.insert fv.toString.toUTF8 ()
              let ⟨_,r,initD,initI⟩ ← withFreeing fv l r initD initI
              go workas initD initI col (.cons d l <| .cons (d+1) r more)
          | .letE _ l r z _ =>
              let fv ← worker d
              let workas := workas.insert fv.toString.toUTF8 ()
              let ⟨_,z,initD,initI⟩ ← withFreeingLet fv l r z initD initI
              go workas initD initI col (.cons d l <| .cons d r <| .cons (d+1) z more)
          | .proj _ _ e => go workas initD initI col (.cons d e more)
          | .mdata _ e => go workas initD initI col (.cons d e more)
          | _ => go workas initD initI col more
      | .enq col enqD enq =>
          match e with
          | .app l r => go workas initD initI col (.cons enqD enq <| .cons d l <| .cons d r more)
          | .lam _ l r _ =>
              let fv ← worker d
              let workas := workas.insert fv.toString.toUTF8 ()
              let ⟨_,r,initD,initI⟩ ← withFreeing fv l r initD initI
              go workas initD initI col (.cons enqD enq <| .cons d l <| .cons (d+1) r more)
          | .forallE _ l r _ =>
              let fv ← worker d
              let workas := workas.insert fv.toString.toUTF8 ()
              let ⟨_,r,initD,initI⟩ ← withFreeing fv l r initD initI
              go workas initD initI col (.cons enqD enq <| .cons d l <| .cons (d+1) r more)
          | .letE _ l r z _ =>
              let fv ← worker d
              let workas := workas.insert fv.toString.toUTF8 ()
              let ⟨_,z,initD,initI⟩ ← withFreeingLet fv l r z initD initI
              go workas initD initI col (.cons enqD enq <| .cons d l <| .cons d r <| .cons (d+1) z more)
          | .proj _ _ e => go workas initD initI col (.cons enqD enq <| .cons d e more)
          | .mdata _ e => go workas initD initI col (.cons enqD enq <| .cons d e more)
          | _ => go workas initD initI col (.cons enqD enq more)
  go {} initD initI initA <| .cons 0 e .nil

@[specialize f, inline]
partial def Lean.Expr.onAllSubtermsFoldNoPartialM (e : Expr) (initD : LocalContext) (initI : LocalInstances)
  {α : Sort _} (init : α) (f : Expr → Nat → CTrie Unit → α → LocalContext → LocalInstances → MetaM (Prod3 α LocalContext LocalInstances))
  : MetaM (Prod3 α LocalContext LocalInstances) :=
  let rec getApp (d : Nat) (as : ListProd Nat Expr) : Expr → ListProd Nat Expr
    | .app l r => getApp d (.cons d r as) l
    | h => .cons d h as
  let rec @[specialize f] go (workas : CTrie Unit) (initD : LocalContext) (initI : LocalInstances) (col : α)
    : ListProd Nat Expr → MetaM (Prod3 α LocalContext LocalInstances)
    | .nil => return ⟨col,initD,initI⟩
    | .cons d e more => do
        let ⟨here,initD,initI⟩  ← f e d workas col initD initI
        match e with
        | .app .. =>
            go workas initD initI (here) (getApp d more e)
        | .lam _ l r _ =>
            let fv ← worker d
            let workas := workas.insert fv.toString.toUTF8 ()
            let ⟨_,r,initD,initI⟩ ← withFreeing fv l r initD initI
            go workas initD initI (here) (.cons d l <| .cons (d+1) r more)
        | .forallE _ l r _ =>
            let fv ← worker d
            let workas := workas.insert fv.toString.toUTF8 ()
            let ⟨_,r,initD,initI⟩ ← withFreeing fv l r initD initI
            go workas initD initI (here) (.cons d l <| .cons (d+1) r more)
        | .letE _ l r z _ =>
            let fv ← worker d
            let workas := workas.insert fv.toString.toUTF8 ()
            let ⟨_,z,initD,initI⟩ ← withFreeingLet fv l r z initD initI
            go workas initD initI (here) (.cons d l <| .cons d r <| .cons (d+1) z more)
        | .proj _ _ e => go workas initD initI (here) (.cons d e more)
        | .mdata _ e => go workas initD initI (here) (.cons d e more)
        | _ => go workas initD initI (here) more
  go {} initD initI init <| .cons 0 e .nil
