

import LeanGrow.Src.Caching.Score.Explore


import LeanGrow.Src.Caching.Score.Test.DummySamples
-- ↑ needed to trigger building olean

open Lean Meta


def mod1 := `LeanGrow.Src.Caching.Score.Test.DummySamples

#check buildConjPosTree_forEnvImportsofModule
#check sampleClass_back_cvbThm_ofModule_S

-- #eval buildConjPosTree_forEnvImportsofModule mod1

-- #eval loadConjPosTree_forTest `Init.Prelude

-- #eval sampleClass_back_cvbThm_ofModule_S 1 2 2 .none .none mod1

#check explore_samClass_thm_core_S

-- #eval explore_samClass_thm_core_S mod1

#check generalize_back_cvbThm_ofModule_S
#check generalize_back_cvbThm_ofModule_inEnv_S


-- #eval generalize_back_cvbThm_ofModule_S mod1

tracing_mode .std
tracing_flags [(`cvb_thms_genGoal, TracingFlags.all),
                (`generalizePaInCore, TracingFlags.all),
                (`generalizePaInCore.go, TracingFlags.all),
                (`generaliseToLnodesCore, TracingFlags.all),
                ]

-- #eval generalize_back_cvbThm_ofModule_inEnv_S mod1

#check sampleClass_back_cvbThm_light_ofModule_S

-- #eval sampleClass_back_cvbThm_light_ofModule_S 1 2 2 .none .none mod1

#check explore_samClass_thm_light_core_S

-- #eval explore_samClass_thm_light_core_S mod1


#check generalize_back_cvbThm_light_ofModule_S

-- #eval generalize_back_cvbThm_light_ofModule_S mod1

#check mkMvarStdIndexNoCoE

/-


When generalised type is function type (∀ and not a prop),
don't look for previous mvar with defeq, but a version of defeq
that looks if the spne matches first.
This should also be noted when cleaning

Thought-dump:
- make sure to use transitive imports for the conjTree loads and builds
  as regular imports don't do the desired job

-/


#check Nat → Nat

def miniTest : MetaM Expr := do
  let lv ← mkFreshLevelMVar
  let mvT ← mkFreshExprMVar (Expr.const `Type [lv])
  let mvF ← mkFreshExprMVar (mvT)
  let lv ← mkFreshLevelMVar
  let mvA ← mkFreshExprMVar (Expr.const `Type [lv])
  let e := Expr.app mvF mvA
  inferType e


-- #eval miniTest
