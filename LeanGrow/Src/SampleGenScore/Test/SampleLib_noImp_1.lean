

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


tracing_mode .std
tracing_flags [(`sampleCoreBack, TracingFlags.all),
               ]

#eval testNoDelZet false `List.disjoint_pmap 1 2 2

-- bad simp (simpParse : simpParse)
