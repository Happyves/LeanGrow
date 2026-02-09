

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


-- tracing_mode .std
-- tracing_flags [(`delabSample_Rewrite_core, TracingFlags.all),
--                (`delabDig_Rewrite_core, TracingFlags.all),
--                (`delabSample_Rewrite_topBack, TracingFlags.all),
--                (`delabSample_Rewrite_topForw, TracingFlags.all),
--                (`sampleCoreForw, TracingFlags.all),
--                ]

-- #eval testNoDelZet false `List.Subset.dedup_append_right 1 2 2

#check List.Subset.union_eq_right
#check List.Subset.trans
#check List.subset_dedup


#check List.filter_comm

-- #eval testNoDelZet false `List.filter_comm 1 2 2


#check List.filter_eq_foldr

-- #eval testNoDelZet false `List.filter_eq_foldr 1 2 2
-- unknonw free var , prbaly forgot to wrap in withLCtx somewhere, but it is lunshtime
