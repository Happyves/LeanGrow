
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Utils.Lean.ImportExport


open Lean System IO FS Process Elab Parser Meta


#check_failure Finset.exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum

unsafe def test2 : IO Unit := do
  withImportModulesTracing #[`Mathlib.Combinatorics.Pigeonhole] {} <| fun env => do
    let .some info := env.find? `Finset.exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum | return "Expr.bvar 42"
    return s!"{info.type}"

-- Workaround, but slows down thing
-- #eval test2



unsafe def test3 : IO Unit := do
  stdImportTracePickle #[`Mathlib.Combinatorics.Pigeonhole] {} "ImportExportTesting_1" do
    let .some info := (← getEnv).find? `Finset.exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum | return (Expr.bvar 42, "fail")
    let T ← inferType info.type
    return (T,"done")


unsafe def test4 : MetaM Unit := do
  stdWithUnpickleTracing Expr "ImportExportTesting_1" <| fun exp => do
    let TT ← inferType exp
    return s!"{TT}"


-- #eval test3
-- #eval test4
