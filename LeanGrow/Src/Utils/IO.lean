/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

unsafe def veryUnsafeIO {α : Type _} [Inhabited α] (fn : IO α) : α :=
  let res := unsafeIO fn
  match res with
  | .ok x => x
  | .error e   => panic s!"veryUnsafeIO raised error:\n{e}"
