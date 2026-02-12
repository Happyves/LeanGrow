

import LeanGrow.Src.Caching.Score.Explore


import LeanGrow.Src.Caching.Score.Test.DummySamples
-- ↑ needed to trigger building olean

open Lean Meta



-- TODO, specialize previous functions, text pipeline

def mod1 := `LeanGrow.Src.Caching.Score.Test.DummySamples

#check buildConjPosTree_forEnvImportsofModule
#check sampleClass_back_cvbThm_ofModule_S

-- #eval buildConjPosTree_forEnvImportsofModule mod1

-- #eval sampleClass_back_cvbThm_ofModule_S 1 2 2 .none .none mod1

#check explore_samClass_thm_core_S


-- #eval explore_samClass_thm_core_S mod1
