

/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

@[extern "extern_export_trick"]
opaque eeTrick : Nat → Nat


/-
# UInt32Array
-/


private opaque UInt32ArrayHelp : NonemptyType
def UInt32Array : Type := UInt32ArrayHelp.type
instance : Nonempty UInt32Array := UInt32ArrayHelp.property


@[extern "lean_u32_array_mk"]
opaque UInt32Array.mk : Array UInt32 → UInt32Array


@[extern "lean_u32_array_data"]
opaque UInt32Array.data : UInt32Array → Array UInt32


namespace UInt32Array


instance : Repr UInt32Array where
  reprPrec := fun x y => reprPrec x.data y

instance : BEq UInt32Array where
  beq := fun x y => x.data == y.data


@[extern "lean_mk_empty_u32_array"]
opaque emptyWithCapacity (c : @& Nat) : UInt32Array

@[inline]
def empty : UInt32Array :=
  emptyWithCapacity 8

instance : Inhabited UInt32Array where
  default :=  empty

instance : EmptyCollection UInt32Array where
  emptyCollection := UInt32Array.empty

@[extern "lean_u32_array_push"]
opaque push : UInt32Array → UInt32 → UInt32Array

@[extern "lean_u32_array_size"]
opaque size : (@& UInt32Array) → Nat

def single (v : UInt32) : UInt32Array :=
  UInt32Array.empty.push v

@[extern "lean_sarray_size"]
opaque usize (a : @& UInt32Array) : USize


-- # Get set

@[extern "lean_u32_array_uget"]
opaque uget : (a : @& UInt32Array) → (i : USize) → i.toNat < a.size → UInt32

@[extern "lean_u32_array_fget"]
opaque get : (ds : @& UInt32Array) → (i : @& Nat) → (h : i < ds.size := by get_elem_tactic) → UInt32

@[extern "lean_u32_array_get"]
opaque get! : (@& UInt32Array) → (@& Nat) → UInt32

@[inline]
def get? (ds : UInt32Array) (i : Nat) : Option UInt32 :=
  if h : i < ds.size then
    some (ds.get i h)
  else
    none

instance : GetElem UInt32Array Nat UInt32 fun xs i => i < xs.size where
  getElem xs i h  := xs.get i h

instance : GetElem UInt32Array USize UInt32 fun xs i => i.toNat < xs.size where
  getElem xs i h := xs.uget i h

@[extern "lean_u32_array_uset"]
opaque uset : (a : UInt32Array) → (i : USize) → UInt32 → (h : i.toNat < a.size := by get_elem_tactic) → UInt32Array

@[extern "lean_u32_array_fset"]
opaque set : (ds : UInt32Array) → (i : @& Nat) → UInt32 → (h : i < ds.size := by get_elem_tactic) → UInt32Array

@[extern "lean_u32_array_set"]
opaque set! : UInt32Array → (@& Nat) → UInt32 → UInt32Array

@[inline]
def isEmpty (s : UInt32Array) : Bool :=
  s.size == 0

@[inline]
partial def toList (ds : UInt32Array) : List UInt32 :=
  let rec loop (i r) :=
    if h : i < ds.size then
      loop (i+1) (ds[i] :: r)
    else
      r.reverse
  loop 0 []

-- # Ordered ops

@[extern "ord_u32_array_contains"]
opaque oContains : (@& UInt32Array) → UInt32 → Bool

@[extern "ord_u32_array_binSearch"]
opaque binSearch : (@& UInt32Array) → UInt32 → Bool

@[extern "ord_u32_array_insert"]
opaque oInsert : UInt32Array → UInt32 → UInt32Array

@[extern "ord_u32_array_binInsert"]
opaque binInsert : UInt32Array → UInt32 → UInt32Array

@[extern "ord_u32_array_hasCommon"]
opaque hasCommon : (@& UInt32Array) → (@& UInt32Array) → Bool

@[extern "ord_u32_array_subsetOf"]
opaque subsetOf : (@& UInt32Array) → (@& UInt32Array) → Bool

@[extern "ord_u32_array_intersect"]
opaque inter : UInt32Array → UInt32Array → UInt32Array

@[extern "ord_u32_array_union"]
opaque union : UInt32Array → UInt32Array → UInt32Array

@[extern "ord_u32_array_hasDiff"]
opaque hasDiff : (@& UInt32Array) → (@& UInt32Array) → Bool

@[extern "ord_u32_array_difference"]
opaque diff : UInt32Array → (@& UInt32Array) → UInt32Array

@[extern "ord_u32_array_sanitize"]
opaque sanitize : UInt32Array →  UInt32Array

@[extern "ord_u32_array_shiftAdd"]
opaque shiftAdd : UInt32Array → UInt32 → UInt32Array

@[extern "ord_u32_array_shiftSub"]
opaque shiftSub : UInt32Array → UInt32 → UInt32Array



-- # Fold


@[inline, specialize]
unsafe def foldlMUnsafe {β : Type v} {m : Type v → Type w} [Monad m]
  (as : UInt32Array) (init : β) (f : UInt32 → β → m β) : m β :=
  let S := USize.ofNat as.size
  let rec @[specialize] fold (i : USize) (b : β) : m β := do
    if i == S then
      pure b
    else
      fold (i+1) (← f (as.uget i lcProof) b)
  fold 0 init


@[implemented_by foldlMUnsafe, expose]
def foldlM {β : Type v} {m : Type v → Type w} [Monad m]
  (as : UInt32Array) (init : β) (f : UInt32 → β → m β) : m β :=
  let rec loop (i : Nat) (j : Nat) (b : β) : m β := do
    if hlt : j < as.size then
      match i with
      | 0    => pure b
      | i'+1 =>
        loop i' (j+1) (← f as[j] b)
    else
      pure b
  loop as.size 0 init


@[inline, expose]
def foldl {β : Type v} (as : UInt32Array) (init : β) (f : UInt32 → β → β) : β :=
  Id.run <| as.foldlM init (pure <| f · ·)





-- # Map


def mapMsafe {m : Type → Type w} [Monad m]
  (f : UInt32 → m UInt32) (as : UInt32Array) : m UInt32Array :=
  let rec map (i : Nat) (bs : UInt32Array) : m UInt32Array := do
      if hlt : i < as.size then
        map (i+1) (bs.push (← f as[i]))
      else
        pure bs
  decreasing_by simp_wf; decreasing_trivial_pre_omega
  map 0 (emptyWithCapacity as.size)


@[extern "u32_array_ptr_get"]
opaque ptr : (@& UInt32Array) → USize

@[extern "u32_array_ptr_read"]
opaque read : USize → UInt32

@[extern "u32_array_ptr_set_next"]
opaque ptrSetNext : USize → UInt32 → USize

@[extern "lean_sarray_deep_copy"]
opaque deepCopy : UInt32Array → UInt32Array


@[inline, specialize]
unsafe def mapSpeMImpl {m : Type → Type w} [Monad m]
  (f : UInt32 → m UInt32) (as : UInt32Array) : m UInt32Array :=
  let sz := as.usize
  let rec @[specialize] map (i ptr : USize) (as : UInt32Array) : m UInt32Array := do
    if i < sz then
     let v := UInt32Array.read ptr
     let w ← f v
     let nptr := UInt32Array.ptrSetNext ptr w
     map (i+1) nptr as
    else
     pure as
  do
  if isExclusiveUnsafe as
  then
    let as ← map 0 as.ptr as
    return as
  else
    let cas := deepCopy as
    let cas ← map 0 cas.ptr cas
    return cas


@[implemented_by mapSpeMImpl, expose]
def mapM {m : Type → Type w} [Monad m]
  (f : UInt32 → m UInt32) (as : UInt32Array) : m UInt32Array :=
  as.mapMsafe f


@[inline, expose]
def map (f : UInt32 → UInt32) (as : UInt32Array) : UInt32Array :=
  Id.run <| as.mapM (pure <| f ·)



-- # Find

@[inline]
def find? (a : UInt32Array) (p : UInt32 → Bool) (start := 0) : Option UInt32 :=
  let rec @[specialize] loop (i : Nat) :=
    if h : i < a.size then
      let v := a[i]
      if p v then some v else loop (i+1)
    else
      none
    termination_by a.size - i
    decreasing_by decreasing_trivial_pre_omega
  loop start

@[inline]
def findIdx? (a : UInt32Array) (p : UInt32 → Bool) (start := 0) : Option Nat :=
  let rec @[specialize] loop (i : Nat) :=
    if h : i < a.size then
      if p a[i] then some i else loop (i+1)
    else
      none
    termination_by a.size - i
    decreasing_by decreasing_trivial_pre_omega
  loop start


-- # For in

@[inline]
unsafe def forInUnsafe {β : Type v} {m : Type v → Type w} [Monad m]
  (as : UInt32Array) (b : β) (f : UInt32 → β → m (ForInStep β)) : m β :=
  let sz := as.usize
  let rec @[specialize] loop (i : USize) (b : β) : m β := do
    if i < sz then
      let a := as.uget i lcProof
      match (← f a b) with
      | ForInStep.done  b => pure b
      | ForInStep.yield b => loop (i+1) b
    else
      pure b
  loop 0 b

@[implemented_by UInt32Array.forInUnsafe]
protected def forIn {β : Type v} {m : Type v → Type w} [Monad m]
  (as : UInt32Array) (b : β) (f : UInt32 → β → m (ForInStep β)) : m β :=
  let rec loop (i : Nat) (h : i ≤ as.size) (b : β) : m β := do
    match i, h with
    | 0,   _ => pure b
    | i+1, h =>
      have h' : i < as.size            := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) h
      have : as.size - 1 < as.size     := Nat.sub_lt (Nat.zero_lt_of_lt h') (by decide)
      have : as.size - 1 - i < as.size := Nat.lt_of_le_of_lt (Nat.sub_le (as.size - 1) i) this
      match (← f as[as.size - 1 - i] b) with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop i (Nat.le_of_lt h') b
  loop as.size (Nat.le_refl _) b

instance : ForIn m UInt32Array UInt32 where
  forIn := UInt32Array.forIn
