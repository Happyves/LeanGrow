

/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Data.Index.Types
import LeanGrow.FFI.Lffi

@[inline]
def idx_UInt32Array : IndexColl UInt32Array where
  reprImpl := inferInstance
  empty := .empty
  isEmpty? := fun x => x.size == 0
  singleton := .single
  size := UInt32Array.size
  contains := UInt32Array.oContains
  hasCommon := UInt32Array.hasCommon
  hasDiff := UInt32Array.hasDiff
  subsetOf := UInt32Array.subsetOf
  insert := UInt32Array.oInsert
  insertFrom := fun O A => A.foldl O (fun x y => UInt32Array.oInsert y x)
  inter := UInt32Array.inter
  union := UInt32Array.union
  diff := UInt32Array.diff
  sanitize := .some <| UInt32Array.sanitize
  mapAddBy := UInt32Array.shiftAdd
  map := UInt32Array.map
  foldl := UInt32Array.foldl
