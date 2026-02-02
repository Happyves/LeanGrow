
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



variable {α β: Sort _} [BEq α] (r : α → α → Prop) [DecidableRel r]


-- # Ordered

@[specialize r]
def List.orderedContainsP  (a : α) : List α → Bool
| [] => false
| x :: l => if r x a then (if x == a then true else (List.orderedContainsP a l)) else false

def List.orderedContains (a : Nat) : List Nat → Bool := List.orderedContainsP (· ≤ ·) a

@[specialize r]
def List.orderedInsertOrLeaveP (a : α) : List α → List α
  | [] => [a]
  | b :: l => if r a b then (if a == b then b :: l else a :: b :: l) else b :: List.orderedInsertOrLeaveP a l

def List.orderedInsertOrLeave (a : Nat) : List Nat → List Nat := List.orderedInsertOrLeaveP (· ≤ ·) a


@[specialize r]
def List.orderedEraseOrLeaveP (a : α) : List α → List α
  | [] => []
  | b :: l => if r a b then (if a == b then l else b :: l) else b :: List.orderedEraseOrLeaveP a l

def List.orderedEraseOrLeave (a : Nat) : List Nat → List Nat := List.orderedEraseOrLeaveP (· ≤ ·) a

@[specialize r]
def List.orderedModifyOrLeaveP (a : α) (f : α → α) : List α → List α
  | [] => []
  | b :: l => if r a b then (if a == b then (f b) :: l else b :: l) else b :: List.orderedModifyOrLeaveP a f l

def List.orderedModifyOrLeave (a : Nat) (f : Nat → Nat) : List Nat → List Nat := List.orderedModifyOrLeaveP (· ≤ ·) a f

-- # intersect

@[specialize r]
def List.orderedIntersectP (a b : List α) : List α :=
  let rec go (inter : List α) : List α → List α → List α
    | [], _ => inter
    | _, [] => inter
    | ah :: aT , bh :: bT =>
        if r ah bh
        then
          if ah == bh
          then go (ah :: inter) aT bT
          else go inter aT (bh :: bT)
        else go inter (ah :: aT) bT
  (go [] a b).reverse

def List.orderedIntersect (a b : List Nat) : List Nat :=
  List.orderedIntersectP (· ≤ ·) a b

-- # union

@[specialize r]
partial def List.orderedUnionP (a b : List α) : List α :=
  let rec go (done : List α) : List α → List α → List α
    | [], B => done.reverse ++ B
    | A, [] => done.reverse ++ A
    | A@(ah :: aT) , B@(bh :: bT) =>
        if r ah bh
        then
          if ah == bh
          then go (ah :: done) aT bT
          else go (ah :: done) aT B
        else go (bh :: done) A bT
  (go [] a b)

def List.orderedUnion (a b : List Nat) : List Nat :=
  List.orderedUnionP (· ≤ ·) a b


@[specialize r]
def List.orderedJoinP (L : List α) : List (List α) → List α
  | [] => L
  | nx :: more => List.orderedJoinP (List.orderedUnionP r nx L) more


def List.orderedJoin (L : List Nat) : List (List Nat) → List Nat :=
  List.orderedJoinP (· ≤ ·) L


/-- a \ b-/
@[specialize r]
partial def List.orderedDiffP (a b : List α) : List α :=
  let rec go (done : List α) : List α → List α → List α
    | [], _ => done.reverse
    | A, [] => done.reverse ++ A
    | A@(ah :: aT) , B@(bh :: bT) =>
        if r ah bh
        then
          if ah == bh
          then go done aT bT
          else go (ah :: done) aT B
        else go done A bT
  (go [] a b)

def List.orderedDiff (a b : List Nat) : List Nat :=
  List.orderedDiffP (· ≤ ·) a b
