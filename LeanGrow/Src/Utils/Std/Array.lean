
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

set_option autoImplicit true


def Array.assignOrFail (eq : α → α → Bool) (i : Nat) (v : α) (A : Array (Option α)) : Option (Array (Option α)) :=
  match A[i]! with
  | .none => .some (A.set! i v)
  | .some w => if eq v w then .some A else .none

def Array.assignOrFailM [Monad m] (eq : α → α → m Bool) (i : Nat) (v : α) (A : Array (Option α)) : m (Option (Array (Option α))) :=
  match A[i]! with
  | .none => return .some (A.set! i v)
  | .some w => do if ← eq v w then return .some A else return .none


/-- Argument `gt` should be `>`-/
@[specialize gt]
def Array.maxInhab (bot : α) (gt : α → α → Bool) (A : Array α) : α :=
  let rec @[specialize gt] go (sofar : α) : Nat → α
    | 0 => sofar
    | n+1 =>
      let a := (A.getD n bot)
      if gt a sofar
      then go a n
      else go sofar n
  go bot A.size


def Array.pushN (A : Array α) (val : α) : Nat → Array α
  | 0 => A
  | n+1 => (A.push val).pushN val n


@[specialize p f]
def Array.findModify (p : α → Bool) (f : α → α) (A : Array α) : Array α :=
  let rec @[specialize p f] go (A : Array α) (i : Nat) : Array α :=
    if h : i < A.size
    then
      let v := A[i]
      if p v
      then A.set i (f v) h
      else go A (i+1)
    else
      A
  go A 0


@[inline]
unsafe def Array.modifyMcpsUnsafe [Monad m] (xs : Array α) (i : Nat)
  (f : α → (α → m β) → m β) (k : (Array α) → m β) : m β := do
  if h : i < xs.size then
    let v                := xs[i]
    -- Replace a[i] by `box(0)`.  This ensures that `v` remains unshared if possible.
    -- Note: we assume that arrays have a uniform representation irrespective
    -- of the element type, and that it is valid to store `box(0)` in any array.
    let xs'               := xs.set i (unsafeCast ())
    f v <| fun v => do
      k <| xs'.set i v (Nat.lt_of_lt_of_eq h (Array.size_set ..).symm)
  else
    k xs

#check Array.modify

@[implemented_by Array.modifyMcpsUnsafe]
def Array.modifyMcps [Monad m] (xs : Array α) (i : Nat)
  (f : α → (α → m β) → m β) (k : (Array α) → m β) : m β := do
  if h : i < xs.size then
    let v   := xs[i]
    f v <| fun v => do
      k <| xs.set i v
  else
    k xs

@[specialize]
def Array.foldlMcps [Monad m] [Inhabited α] [Inhabited β] (xs : Array α)
  (f : α → (β → m γ) → m γ) (k : (Array β) → m γ) : m γ :=
  let out : Array β := Array.replicate xs.size default
  let rec @[specialize] go (i : Nat) (out : Array β) (k : (Array β) → m γ) : m γ :=
    if i < out.size
    then
      f xs[i]! <| fun b => do
        go (i+1) (out.set! i b) k
    else
      k out
  go 0 out k

@[specialize]
def Array.foldlMcps' [Monad m] [Inhabited α] (xs : Array α) (init : β)
  (f : α → β → (β → m γ) → m γ) (k : β → m γ) : m γ :=
  let rec @[specialize] go (i : Nat) (out : β) (k : β → m γ) : m γ :=
    if i < xs.size
    then
      f xs[i]! out <| fun b => do
        go (i+1) b k
    else
      k out
  go 0 init k
