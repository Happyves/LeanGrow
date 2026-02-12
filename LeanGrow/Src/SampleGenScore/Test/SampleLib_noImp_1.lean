

import LeanGrow.Src.SampleGenScore.Test.SampleForw
import LeanGrow.Src.SampleGenScore.Test.SampleBack

import Mathlib.Data.List.Lemmas

open Lean Meta

set_option linter.style.longLine false



def testNoDelZet (printLift? : Bool) (thmName : Name) (depthDig depthStart depthStop : Nat) : MetaM Unit := do
  testNoDelZet_B printLift? thmName depthDig depthStart depthStop
  testNoDelZet_F printLift? thmName depthDig depthStart depthStop
  testNoDelZet_wH_F printLift? thmName depthDig depthStart depthStop

def testDelZet (printLift? : Bool) (thmName : Name)
  (depthDig depthStart depthStop deltaFuel zetaFuel : Nat) : MetaM Unit := do
  testDelZet_B printLift? thmName depthDig depthStart depthStop deltaFuel zetaFuel
  testDelZet_F printLift? thmName depthDig depthStart depthStop deltaFuel zetaFuel
  testNoDelZet_wH_F printLift? thmName depthDig depthStart depthStop


#check 1

#print List.Subset.dedup_append_right

-- #eval testNoDelZet false `List.Subset.dedup_append_right 1 2 2

#check List.Subset.union_eq_right
#check List.Subset.trans
#check List.subset_dedup


#check List.filter_comm

-- #eval testNoDelZet false `List.filter_comm 1 2 2


#check List.filter_eq_foldr

-- tracing_mode .std
-- tracing_flags [(`sampleCoreForw, TracingFlags.all),
--                ]

-- #eval testNoDelZet false `List.filter_eq_foldr 1 2 2


#check List.length_erase_add_one

-- #eval testNoDelZet false `List.length_erase_add_one 1 2 2


#check List.forall_map_iff

-- #eval testNoDelZet false `List.forall_map_iff 1 2 2


#check List.Forall.imp


-- #eval testNoDelZet false `List.Forall.imp 1 2 2


#print List.disjoint_pmap

-- #eval testNoDelZet false `List.disjoint_pmap 1 2 2


#check List.Perm.disjoint_right


-- #eval testNoDelZet false `List.Perm.disjoint_right 1 2 2


#check List.range'_0


-- #eval testNoDelZet false `List.range'_0 1 2 2


#check List.left_le_of_mem_range'


-- #eval testNoDelZet false `List.left_le_of_mem_range' 1 2 2


#check List.map_erase


-- #eval testNoDelZet false `List.map_erase 1 2 2


#print  List.injOn_insertIdx_index_of_notMem


-- #eval testNoDelZet false `List.injOn_insertIdx_index_of_notMem 1 2 2


#print List.injOn_insertIdx_index_of_notMem._simp_1_4


-- tracing_mode .std
-- tracing_flags [(`delabTopBack, TracingFlags.all),
--                 (`delab_simpGoal, TracingFlags.all)
--                ]
