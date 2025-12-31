
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

variable {α β: Sort _} [BEq α] (r : α → α → Prop) [DecidableRel r]


-- # Sorting

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


-- # noOrder

-- def List.insertOrLeave (a : α) : List α → List α
--   | [] => [a]
--   | b :: l => if a == b then b :: l else b :: List.insertOrLeave a l

-- /-- Assumes the list has no duplicates of the elemenent to be erased-/
-- def List.eraseOrLeave (a : α) : List α → List α
--   | [] => []
--   | b :: l => if a == b then l else b :: List.eraseOrLeave a l


-- # headD_tail

-- def List.headD_tail (l : List α) (default : α) : α × List α :=
--   match l with
--   | [] => (default, [])
--   | h :: t => (h,t)


-- # reduce or fail

-- def List.reduceOptionOrFail : List (Option α) →  Option (List α)
-- | [] => .some []
-- | .some x :: l => (x :: ·) <$> (List.reduceOptionOrFail l)
-- | .none :: _ => .none

-- @[specialize p modify]
-- def List.findModify (p : α → Bool) (modify : α → α) : List α → List α
-- | [] => []
-- | x :: l => if p x then (modify x) :: l else x :: (List.findModify p modify l)

-- @[specialize p modify add]
-- def List.findModifyAdd (p : α → Bool) (modify : α → α) (add : α) : List α → List α
-- | [] => [add]
-- | x :: l => if p x then (modify x) :: l else x :: (List.findModifyAdd p modify add l)

-- @[specialize p modify add]
-- def List.findModifyAddDelete (p : α → Bool) (modify : α → Option α) (add : α) : List α → List α
-- | [] => [add]
-- | x :: l =>
--   if p x
--   then
--     match (modify x) with
--     | .some y => y:: l
--     | _ => l
--   else x :: (List.findModifyAddDelete p modify add l)

-- set_option autoImplicit true in
-- @[specialize p modify add]
-- def List.findModifyAddDeleteM [Monad m] (p : α → Bool) (modify : α → m (Option α)) (add : α) : List α → m (List α)
-- | [] => return [add]
-- | x :: l => do
--   if p x
--   then
--     match (← modify x) with
--     | .some y => return y :: l
--     | _ => return l
--   else return x :: (← List.findModifyAddDeleteM p modify add l)

-- set_option autoImplicit true in
-- @[specialize p modify add]
-- def List.findModifyAddDeleteInfoM [Monad m] (p : α → Bool) (modify : α → m (Option α)) (add : α) : List α → m (Bool × List α)
-- | [] => return (false,[add])
-- | x :: l => do
--   if p x
--   then
--     match (← modify x) with
--     | .some y => return (false, y :: l)
--     | _ => return (true,l)
--   else
--     let (del?,res) ← List.findModifyAddDeleteInfoM p modify add l
--     return (del?, x :: res)


-- set_option autoImplicit true in
-- @[specialize p modify add]
-- def List.findModifyAddFailM [Monad m] (p : α → Bool) (modify : α → m (Option α)) (add : α) : List α → m (Option (List α))
-- | [] => return [add]
-- | x :: l => do
--   if p x
--   then
--     match (← modify x) with
--     | .some y => return y :: l
--     | _ => return .none
--   else return (x :: · ) <$> (← List.findModifyAddFailM p modify add l)


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


-- # findD

@[specialize p default]
def List.findD (p : α → Bool) (default : α) : List α → α
| [] => default
| x :: l => if p x then x else l.findD p default




-- # misc

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


-- @[specialize f]
-- def List.mapTRRMcps
--   {m} [Monad m]
--   {β γ : Sort _} (l : List α) (f : α → (β → m γ) →  m γ)
--   (k : List β → m γ) : m γ :=
--   let rec go (done : List β) (k : List β → m γ) : List α → m γ
--     | [] => k done
--     | x :: xs => do
--         f x <| fun res => do
--           go ( res :: done) k xs
--   go [] k l

/-- Doesn't maintain order -/
def List.findDelete (a : α) (l : List α) : Bool × List α :=
  let rec go (done : List α) : List α → Bool × List α
    | [] => (false,done)
    | b :: l => if a == b then (true, done ++ l) else go (b :: done) l
  go [] l


-- def List.snoc (a : α) (l : List α) :  List α :=
--   match l with
--   | .nil => .cons a l
--   | .cons x L => .cons x <| L.snoc a

def List.snocTR (a : α) (l : List α) :  List α :=
  (a :: l.reverse).reverse

-- # difference

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
