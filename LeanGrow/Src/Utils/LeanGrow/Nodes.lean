
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Lean.Expr

import Lean

open Lean

def gnode (i : Nat) : Name := .num `g i

def unode (i : Nat) : Name := .num `u i

def lnode (module : Name) (thmIdx pos : Nat) : Name := .num (.num module thmIdx) pos

def tnode (backIdx pos : Nat) : Name := .num (.num `t backIdx) pos

def worker (i : Nat) {m} [Monad m] [MonadNameGenerator m] : m Name := do
  let pre ← mkFreshId
  return .num (.str pre "w") i

def Lean.FVarId.isWorker (i : FVarId) : Bool :=
  match i.name with
  | .num (.str _ k) _ =>  k == "w"
  | _ => false

def Lean.FVarId.isUnode (i : FVarId) : Bool :=
  match i.name with
  | .num k _ =>  k == `u
  | _ => false


def Lean.FVarId.isTnode (i : FVarId) : Bool :=
  match i.name with
  | .num (.num _ _) _ =>  true
  | _ => false

@[inline]
def ifGNode (e : Expr) {α : Sort _} (pos : Nat → α) (neg : α) : α :=
  match e with
  | .fvar ⟨.num k i⟩ =>
      if k == `g
      then pos i
      else neg
  | _ => neg
