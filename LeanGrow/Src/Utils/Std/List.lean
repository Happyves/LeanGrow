
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/



@[specialize p default]
def List.findD (p : α → Bool) (default : α) : List α → α
| [] => default
| x :: l => if p x then x else l.findD p default

partial def List.Ico (sta sto : Nat) : List Nat :=
  let rec go (done : List Nat) (add : Nat) : List Nat :=
    if add ≤ sta then add :: done else go (add :: done) (add - 1)
  if sta < sto
  then go [] (sto - 1)
  else []

/-- Tail recursive map that reverses list order-/
@[specialize f]
def List.mapTRR {β : Sort _} (l : List α) (f : α → β) : List β :=
  let rec go (done : List β) : List α → List β
    | [] => done
    | x :: xs => go (f x :: done) xs
  go [] l

/-- Tail recursive map that reverses list order-/
@[specialize f]
def List.mapTRRM
  {m} [Monad m]
  {β : Sort _} (l : List α) (f : α → m β) : m (List β) :=
  let rec go (done : List β) : List α → m (List β)
    | [] => return done
    | x :: xs => do go ((← f x) :: done) xs
  go [] l



/-- Doesn't maintain order -/
def List.findDelete [BEq α] (a : α) (l : List α) : Bool × List α :=
  let rec go (done : List α) : List α → Bool × List α
    | [] => (false,done)
    | b :: l => if a == b then (true, done ++ l) else go (b :: done) l
  go [] l


def List.snocTR (a : α) (l : List α) :  List α :=
  (a :: l.reverse).reverse
