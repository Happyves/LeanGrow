

/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


structure IndexColl (Impl : Type) where
  reprImpl : Repr Impl
  empty : Impl
  isEmpty? : Impl → Bool
  singleton : UInt32 → Impl
  size : Impl → Nat
  contains : Impl → UInt32 → Bool
  hasCommon : Impl → Impl → Bool
  hasDiff : Impl → Impl → Bool
  subsetOf : Impl → Impl → Bool
  insert : Impl → UInt32 → Impl
  insertFrom : Impl → Impl → Impl
  inter : Impl → Impl → Impl
  union : Impl → Impl → Impl
  diff : Impl → Impl → Impl
  sanitize : Option (Impl → Impl)
  mapAddBy : Impl → UInt32 → Impl
  map : (UInt32 → UInt32) → Impl → Impl
  foldl : {β : Type} → Impl → β → (UInt32 → β → β) → β


instance (Impl : Type) (I : IndexColl Impl) : Repr Impl := I.reprImpl
