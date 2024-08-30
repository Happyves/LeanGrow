-- This module serves as the root of the `LeanGrow` library.
-- Import modules here that should be built as part of the library.
--import LeanGrow.AbstractLocalContext
import LeanGrow.Blacklisting
import LeanGrow.CExpr
--import LeanGrow.Clustering
import LeanGrow.DAGembed
import LeanGrow.DAGstruct
-- import LeanGrow.Frontend_Mark1
-- import LeanGrow.Frontend_Mark2
--import LeanGrow.Frontend_Nomeclature
import LeanGrow.NameListCompare
import LeanGrow.Nomeclature
import LeanGrow.ProcessDecl
import LeanGrow.ProcessEnv_forFrontEnd_2
import LeanGrow.ProcessLocalCtx
import LeanGrow.Test
--import LeanGrow.Caches.mark2cache_v2
--import LeanGrow.Caches.mark2clusters

import LeanGrow.Caches.mark2cache_v2_big
import LeanGrow.Caches.mark1goalCache_big
-- import LeanGrow.CoClustering
-- import LeanGrow.Caches.CoData
-- import LeanGrow.Caches.goalCoData
-- import LeanGrow.Caches.CoData_qt
import LeanGrow.Caches.Querytree
import LeanGrow.Caches.QuerytreeGoal
--import LeanGrow.Caches.QueryTreeSmoothClusters
import LeanGrow.Caches.QueryTreeSmoothClusters_wL_col2
import LeanGrow.Caches.QueryTreeSmoothClustersGoal_wL_col2

--import LeanGrow.Caches.SmolTransitionGraphs
-- don 't import ↑ and ↓ together
import LeanGrow.Caches.LargeTransitionGraphs


-- import LeanGrow.Caches.SmolTransitionGraphClosure_clos_3
import LeanGrow.Caches.LargeTransitionGraphClosure_clos_3

-- import LeanGrow.Caches.SmolTransitionGraphClosure_rbt_clos_3
-- import LeanGrow.Caches.LargeTransitionGraphClosure_rbt_clos_3

-- import LeanGrow.Caches.QueryTreeSmoothClustersHuge_g_wL_col2
-- import LeanGrow.Caches.QueryTreeSmoothClustersHuge_wL_col2

import LeanGrow.Frontend_Mark3
