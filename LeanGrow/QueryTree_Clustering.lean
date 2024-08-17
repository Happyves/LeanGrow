
import LeanGrow.QueryTree
import LeanGrow.Caches.mark2cache_v2_big

open Lean Data

elab "make_queryTree_clusters" : command => do
  let trie_list := cluster_list.map pdata.sink_cst_names
  let res := QueryTree.make trie_list
  let source := s!"import LeanGrow.QueryTree\nopen Lean Data\n def tha_tree : QueryTree := {QueryTree.toString res}"
  IO.FS.writeFile ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/Querytree.lean"⟩ (source)


--make_queryTree_clusters
