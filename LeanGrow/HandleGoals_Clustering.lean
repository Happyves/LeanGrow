
import LeanGrow.Caches.mark1goalCache

open Lean Data

def process (pd : gdata) (flag : Bool) (fact_cluster : ( (List gdata))): List (Trie Unit × (List gdata)) → (List (Trie Unit × (List gdata)) × ((List gdata)))
| [] => if flag then ([],[]) else (if ( Nat.toFloat (Trie.size pd.name_list)) == 0 then ([], pd :: fact_cluster) else ([(pd.name_list, [pd])], []))
| c :: cs =>
    let S := ( Nat.toFloat (Trie.size pd.name_list)) -- cache size in gdata!
    if S == 0
    then
      let (clu, facz) := (process pd flag fact_cluster cs)
      (c:: clu, facz)
    else
      let common := Trie.CountCommon pd.name_list c.1
      let ratio := ( Nat.toFloat common ) / S
      -- v1
      -- if ratio ≥ 0.33
      -- then  let merged_trie := Trie.merge pd.name_list c.1
      --       let clust := pd :: c.2
      --       if ratio ≥ 0.66
      --       then let (clu, facz) := (process pd true fact_cluster cs) ; ((merged_trie, clust) :: clu, facz)
      --       else let (clu, facz) := (process pd flag fact_cluster cs) ; ((merged_trie, clust) :: clu, facz)
      -- else let (clu, facz) := (process pd flag fact_cluster cs) ; (c :: clu, facz)
      -- v2
      if ratio ≥ 0.5
      then  let merged_trie := Trie.merge pd.name_list c.1
            let clust := pd :: c.2
            let (clu, facz) := (process pd true fact_cluster cs)
            ((merged_trie, clust) :: clu, facz)
      else let (clu, facz) := (process pd flag fact_cluster cs)
           (c :: clu, facz)


def cluster : List gdata → (List (Trie Unit × (List gdata)) × ((List gdata)))
| [] => ([], [])
| pd :: rest =>
    let (sofar_c, sofar_f) := cluster rest
    process pd false sofar_f sofar_c



elab "make_cluster" : command => do
  let preres := cluster goal_cluster_list
  let res := (Trie.empty , preres.2) :: preres.1
  let printit := res.map (fun (t,l) => s!"⟨{print_trie t}, [{String.intercalate "," (l.map (fun p => "GDATA." ++ p.cst_name.toString))}]⟩")
  let (package, cluster_num) := printit.foldl (fun (s,count) d => ((s!"\ndef cluster_{count} : Trie Unit × (List gdata) := " ++ d) :: s, count+1)) ([""],0)
  let cl_L := s!"\ndef g_cl_L : List (Trie Unit × (List gdata)) := [{String.intercalate "," ((List.range printit.length).map (fun n => s!"cluster_{n}"))}]"
              -- else return hmm) ["import Caches.mark2cache_v2\n"]
  let source := "import LeanGrow.Caches.mark1goalCache\nopen Lean Data\n" ++ ((String.join package) ++  cl_L)
  IO.FS.writeFile ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/mark1goalClusters.lean"⟩ (source)

-- produces file that fails to lakebuild even with increased maxHeartbeat XD
-- I used to prenit the whole gdata in teh clusters, instead of mentioning their names
--make_cluster
