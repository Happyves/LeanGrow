

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

-- #eval generalize_back_cvbThm_ofModule_inEnv_S mod1


#check explore_gen_thm_core_S


-- #eval explore_gen_thm_core_S mod1


#check sampleClass_back_cvbGoalHyp_ofModule_S


-- #eval sampleClass_back_cvbGoalHyp_ofModule_S 1 2 2 .none .none mod1


#check explore_samClass_gh_core_S

-- #eval explore_samClass_gh_core_S mod1



#check generalize_back_cvbGoalHyp_ofModule_S
#check generalize_back_cvbGoalHyp_ofModule_inEnv_S


-- #eval generalize_back_cvbGoalHyp_ofModule_S mod1
-- ↑ panics but ↓ doesn't ...
-- #eval generalize_back_cvbGoalHyp_ofModule_inEnv_S mod1


#check explore_gen_gh_core_S


-- #eval explore_gen_gh_core_S mod1


/-


TODO
- test query subpat
- query conj (+lg embed and non-lg-embed)



Thought-dump:
- make sure to use transitive imports for the conjTree loads and builds
  as regular imports don't do the desired job


Long term:
- separate instance and non-instance hyps, so that we can try to syth the latter
  at query if it's not in ltx. Alternatively, just ignore instances ...
-/
