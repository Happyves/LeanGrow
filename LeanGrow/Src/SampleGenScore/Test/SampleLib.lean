

import LeanGrow.Src.SampleGenScore.Test.SampleForw
import LeanGrow.Src.SampleGenScore.Test.SampleBack
import LeanGrow.Src.Utils.Lean.ImportExport

import Mathlib.Data.List.Lemmas

open Lean Meta

set_option linter.style.longLine false


#check WithImportModules
#check withImportModulesTracing


unsafe def testNoDelZet (printLift? : Bool) (modName thmName : Name) (depthDig depthStart depthStop : Nat) : IO Unit := do
  WithImportModules #[modName] {} <| fun env => do
    stdMetaRun env <| do
      testNoDelZet_B printLift? thmName depthDig depthStart depthStop
      testNoDelZet_F printLift? thmName depthDig depthStart depthStop

unsafe def testDelZet (printLift? : Bool) (modName thmName : Name)
  (depthDig depthStart depthStop deltaFuel zetaFuel : Nat) : IO Unit := do
  WithImportModules #[modName] {} <| fun env => do
    stdMetaRun env <| do
      testDelZet_B printLift? thmName depthDig depthStart depthStop deltaFuel zetaFuel
      testDelZet_F printLift? thmName depthDig depthStart depthStop deltaFuel zetaFuel

unsafe def testNoDelZet_inEnv (printLift? : Bool) (thmName : Name) (depthDig depthStart depthStop : Nat) : MetaM Unit := do
    testNoDelZet_B printLift? thmName depthDig depthStart depthStop
    testNoDelZet_F printLift? thmName depthDig depthStart depthStop

#check 1


#print List.drop_nil

-- #eval testNoDelZet false `Init.Data.List.Basic `List.drop_nil 1 2 2


#print List.Subset.dedup_append_right

-- #eval testNoDelZet false `Mathlib.Data.List.Dedup `List.Subset.dedup_append_right 1 2 2


#check List.filter_comm

-- #eval testNoDelZet false `Mathlib.Data.List.Basic `List.filter_comm 1 1 1

-- #eval testNoDelZet false `Mathlib.Data.List.Basic `List.filter_comm 1 2 2


#check List.filter_eq_foldr

-- #eval testNoDelZet false `Mathlib.Data.List.Basic `List.filter_eq_foldr 1 1 1

-- #eval testNoDelZet false `Mathlib.Data.List.Basic `List.filter_eq_foldr 1 2 2


#check List.length_erase_add_one

-- #eval testNoDelZet false `Mathlib.Data.List.Basic `List.length_erase_add_one 1 1 1
-- wierd decide

-- #eval testNoDelZet false `Mathlib.Data.List.Basic `List.length_erase_add_one 1 2 2

#check List.forall_map_iff

-- #eval testNoDelZet false `Mathlib.Data.List.Basic `List.forall_map_iff 1 1 1

-- #eval testNoDelZet false `Mathlib.Data.List.Basic `List.forall_map_iff 1 2 2

#check List.disjoint_pmap

-- #eval testNoDelZet false `Mathlib.Data.List.Basic `List.disjoint_pmap 1 1 1

-- #eval testNoDelZet false `Mathlib.Data.List.Basic `List.disjoint_pmap 1 2 2


#check List.Perm.disjoint_right

-- #eval testNoDelZet false `Mathlib.Data.List.Basic `List.Perm.disjoint_right 1 1 1

-- #eval testNoDelZet false `Mathlib.Data.List.Basic `List.Perm.disjoint_right 1 2 2


#check List.range'_0

-- #eval testNoDelZet false `Mathlib.Data.List.Basic `List.range'_0 1 1 1

-- #eval testNoDelZet false `Mathlib.Data.List.Basic `List.range'_0 1 2 2


#check List.left_le_of_mem_range'

-- #eval testNoDelZet false `Mathlib.Data.List.Basic `List.left_le_of_mem_range' 1 1 1

-- #eval testNoDelZet false `Mathlib.Data.List.Basic `List.left_le_of_mem_range' 1 2 2


#check List.map_erase

-- #eval testNoDelZet false `Mathlib.Data.List.Basic `List.map_erase 1 2 2


-- # stress-test

#check List.injOn_insertIdx_index_of_notMem
#print List.injOn_insertIdx_index_of_notMem


-- #eval testNoDelZet false_inEnv `List.injOn_insertIdx_index_of_notMem 1 2 2


-- #eval testNoDelZet false `Mathlib.Data.List.Lemmas `List.injOn_insertIdx_index_of_notMem 1 1 1

-- #eval testNoDelZet true `Mathlib.Data.List.Lemmas `List.injOn_insertIdx_index_of_notMem 1 2 2
-- *Note* the non-β'ed hyps are due to introing `Set.InjOn`, where they arise "naturally"

-- TODO:
-- still lots of bad Eq.mp and id ...
-- Litterally all relevant lemmata are missing as samples:
-- Set.mem_singleton_iff, Set.setOf_eq_eq_singleton, Set.mem_setOf_eq, List.mem_cons,
-- List.insertIdx_succ_cons, Nat.succ_le_succ_iff
-- Although, some like `insertIdx_succ_cons` are in the simp call
-- but don't actually make it into the term

#check List.foldr_range_subset_of_range_subset

-- #eval testNoDelZet false `Mathlib.Data.List.Lemmas `List.foldr_range_subset_of_range_subset 1 1 1

-- #eval testNoDelZet false `Mathlib.Data.List.Lemmas `List.foldr_range_subset_of_range_subset 1 2 2


-- good stress test : combinatorial nullstellensatz


#check List.injOn_insertIdx_index_of_notMem._simp_1_4
#print List.injOn_insertIdx_index_of_notMem._simp_1_4
#print List.injOn_insertIdx_index_of_notMem._simp_1_3
#print List.injOn_insertIdx_index_of_notMem._simp_1_2
#print List.injOn_insertIdx_index_of_notMem._simp_1_1
#print Set.mem_singleton_iff._simp_1
