

import LeanGrow.ProcessEnv_forFrontEnd_2
import LeanGrow.Caches.mark2cache_v2



open Lean Data




def process (pd : pdata) (flag : Bool) (fact_cluster : ( (List pdata))): List (Trie Unit × (List pdata)) → (List (Trie Unit × (List pdata)) × ((List pdata)))
| [] => if flag then ([],[]) else  (if (Trie.size pd.sink_cst_names) == 0 then ([], [pd]) else ([(pd.sink_cst_names, [pd])], []))
| c :: cs =>
    let common := Trie.CountCommon pd.sink_cst_names c.1
    let S := ( Nat.toFloat (Trie.size pd.sink_cst_names)) -- cache size in pdata!
    if S == 0
    then
      let (clu, facz) := (process pd flag fact_cluster cs)
      (clu, pd :: facz)
    else
      let ratio := ( Nat.toFloat common ) / S
      -- v1
      -- if ratio ≥ 0.33
      -- then  let merged_trie := Trie.merge pd.sink_cst_names c.1
      --       let clust := pd :: c.2
      --       if ratio ≥ 0.66
      --       then let (clu, facz) := (process pd true fact_cluster cs) ; ((merged_trie, clust) :: clu, facz)
      --       else let (clu, facz) := (process pd flag fact_cluster cs) ; ((merged_trie, clust) :: clu, facz)
      -- else let (clu, facz) := (process pd flag fact_cluster cs) ; (c :: clu, facz)
      -- v2
      if ratio ≥ 0.80
      then  let merged_trie := Trie.merge pd.sink_cst_names c.1
            let clust := pd :: c.2
            let (clu, facz) := (process pd true fact_cluster cs)
            ((merged_trie, clust) :: clu, facz)
      else let (clu, facz) := (process pd flag fact_cluster cs)
           (c :: clu, facz)


def cluster : List pdata → (List (Trie Unit × (List pdata)) × ((List pdata)))
| [] => ([], [])
| pd :: rest =>
    let (sofar_c, sofar_f) := cluster rest
    process pd false sofar_f sofar_c



elab "make_cluster" : command => do
  let preres := cluster cluster_list
  let res := (Trie.empty , preres.2) :: preres.1
  let printit := res.map (fun (t,l) => s!"⟨{print_trie t}, [{String.intercalate "," (l.map (fun p => "PDATA." ++ p.cst_name.toString))}]⟩")
  let (package, cluster_num) := printit.foldl (fun (s,count) d => ((s!"\ndef cluster_{count} : Trie Unit × (List pdata) := " ++ d) :: s, count+1)) ([""],0)
  let cl_L := s!"\ndef cl_L : List (Trie Unit × (List pdata)) := [{String.intercalate "," ((List.range printit.length).map (fun n => s!"cluster_{n}"))}]"
              -- else return hmm) ["import Caches.mark2cache_v2\n"]
  let source := "import LeanGrow.Caches.mark2cache_v2\nopen Lean Data\n" ++ ((String.join package) ++  cl_L)
  IO.FS.writeFile ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/mark2clusters_v2.lean"⟩ (source)

-- produces file that fails to lakebuild even with increased maxHeartbeat XD
-- I used to prenit the whole pdata in teh clusters, instead of mentioning their names
--make_cluster
