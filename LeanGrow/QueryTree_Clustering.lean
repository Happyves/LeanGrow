
import LeanGrow.QueryTree
import LeanGrow.Caches.mark2cache_v2_big

open Lean Data

elab "make_queryTree_clusters" : command => do
  let trie_list := cluster_list.map pdata.sink_cst_names
  let res := (QueryTree.make trie_list : QueryTree Unit)
  let source := s!"import LeanGrow.QueryTree\nopen Lean Data\n def tha_tree : QueryTree := {QueryTree.toString (fun _ => "()") res}"
  IO.FS.writeFile ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/Querytree.lean"⟩ (source)


--make_queryTree_clusters


set_option maxRecDepth 100000000000000
set_option maxHeartbeats 0

--#eval (QueryTree.visualize 0 (QueryTree.make ((cluster_list.take 100).map pdata.sink_cst_names))).toFormat
-- crash


--#eval (QueryTree.visualize 0 ((QueryTree.make_bd_iter 0 ((cluster_list).map pdata.sink_cst_names)) : QueryTree Unit)).toFormat
-- works

--#eval (QueryTree.visualize 0 ((QueryTree.make_bd_iter 1 ((cluster_list).map pdata.sink_cst_names)) : QueryTree Unit)).toFormat
-- crash

--#eval (QueryTree.visualize 0 ((QueryTree.make_bd_iter_two_electric_boogaloo 0 ((cluster_list).map pdata.sink_cst_names)) : QueryTree Unit)).toFormat
-- works

--#eval (QueryTree.visualize 0 ((QueryTree.make_bd_iter_two_electric_boogaloo 1 ((cluster_list).map pdata.sink_cst_names)) : QueryTree Unit)).toFormat
-- works

--#eval (QueryTree.visualize 0 ((QueryTree.make_bd_iter_two_electric_boogaloo 2 ((cluster_list).map pdata.sink_cst_names)) : QueryTree Unit)).toFormat
-- crash

--#eval cluster_list.length
