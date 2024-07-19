

import LeanGrow.ProcessEnv_forFrontEnd_2
import LeanGrow.Caches.mark2cache_v2



open Lean Data




def process (pd : pdata) (flag : Bool) (fact_cluster : ( (List pdata))) (count len : Nat): List (Trie Unit × (List pdata)) → (List (Trie Unit × (List pdata)) × ((List pdata)))
| [] => if flag then ([],[]) else (if ( Nat.toFloat (Trie.size pd.sink_cst_names)) == 0 then ([], pd :: fact_cluster) else ([(pd.sink_cst_names, [pd])], []))
| c :: cs =>
    if count ≤ (len / 4)
    then
      let S := ( Nat.toFloat (Trie.size pd.sink_cst_names)) -- cache size in pdata!
      if S == 0
      then
        let (clu, facz) := (process pd flag fact_cluster (count) len cs)
        (c :: clu, facz)
      else
        let common := Trie.CountCommon pd.sink_cst_names c.1
        let ratio := ( Nat.toFloat common ) / (min S (Nat.toFloat (Trie.size c.1)))
        -- v1
        -- if ratio ≥ 0.33
        -- then  let merged_trie := Trie.merge pd.sink_cst_names c.1
        --       let clust := pd :: c.2
        --       if ratio ≥ 0.66
        --       then let (clu, facz) := (process pd true fact_cluster cs) ; ((merged_trie, clust) :: clu, facz)
        --       else let (clu, facz) := (process pd flag fact_cluster cs) ; ((merged_trie, clust) :: clu, facz)
        -- else let (clu, facz) := (process pd flag fact_cluster cs) ; (c :: clu, facz)
        -- v2
        if ratio ≥ 0.8
        then  let merged_trie := Trie.merge pd.sink_cst_names c.1
              let clust := pd :: c.2
              let (clu, facz) := (process pd true fact_cluster (count + 1) len cs)
              ((merged_trie, clust) :: clu, facz)
        else let (clu, facz) := (process pd flag fact_cluster (count) len cs)
            (c :: clu, facz)
    else
      let (clu, facz) := (process pd true fact_cluster (count) len cs)
      (c :: clu, facz)

def cluster : List pdata → (List (Trie Unit × (List pdata)) × ((List pdata)))
| [] => ([], [])
| pd :: rest =>
    let (sofar_c, sofar_f) := cluster rest
    process pd false sofar_f 0 sofar_c.length sofar_c


def phase_two  (clu : List pdata) : (List (Trie Unit × (List pdata))):=
  let inters :=
    match clu with
    | [] => Trie.empty
    | _ => clu.tail.foldl (fun I t => Trie.intersect I t.sink_cst_names) clu.head!.sink_cst_names

  let rec c :  List pdata → (List (Trie Unit × (List pdata)) × ((List pdata)))
    | [] => ([], [])
    | pd :: rest =>
        let (sofar_c, sofar_f) := c rest
        process {pd with sink_cst_names := Trie.filter pd.sink_cst_names inters} false sofar_f 0 sofar_c.length sofar_c

  let (petals, core) := c clu
  (inters, core) :: petals



--#exit


elab "make_cluster" : command => do
  -- v1
  --let preres := cluster cluster_list
  --let res := (Trie.empty , preres.2) :: preres.1
  -- v2
  let (preres, eres) := cluster cluster_list
  let res := (Trie.empty , eres) :: (List.join (preres.map (fun c => phase_two c.2)))
  -- common
  let printit := res.map (fun (t,l) => s!"⟨{print_trie t}, [{String.intercalate "," (l.map (fun p => "PDATA." ++ p.cst_name.toString))}]⟩")
  let (package, cluster_num) := printit.foldl (fun (s,count) d => ((s!"\ndef cluster_{count} : Trie Unit × (List pdata) := " ++ d) :: s, count+1)) ([""],0)
  let cl_L := s!"\ndef cl_L : List (Trie Unit × (List pdata)) := [{String.intercalate "," ((List.range printit.length).map (fun n => s!"cluster_{n}"))}]"
  let source := "import LeanGrow.Caches.mark2cache_v2\nopen Lean Data\n" ++ ((String.join package) ++  cl_L)
  IO.FS.writeFile ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/mark2clusters_v2.lean"⟩ (source)

-- produces file that fails to lakebuild even with increased maxHeartbeat XD
-- I used to prenit the whole pdata in teh clusters, instead of mentioning their names
--make_cluster
