
import LeanGrow.Caches.mark1goalCache

open Lean Data

def process (pd : gdata) (flag : Bool) (fact_cluster : ( (List gdata))) (count len : Nat): List (Trie Unit × (List gdata)) → (List (Trie Unit × (List gdata)) × ((List gdata)))
| [] =>
  --dbg_trace s!"Final step of process phase reached with flag {flag}"
  if flag then ([],[]) else (if ( Nat.toFloat (Trie.size pd.name_list)) == 0 then ([], pd :: fact_cluster) else ([(pd.name_list, [pd])], []))
| c :: cs =>
    --dbg_trace s!"Instepcting cluster with name list {Trie.print_keys ⟨#[]⟩ c.1}"
    if count ≤ (len / 4)
    then
      let S := ( Nat.toFloat (Trie.size pd.name_list)) -- cache size in gdata!
      if S == 0
      then -- this whole part should be moved out of recursion!
        --dbg_trace s!"Empty name list → skipping"
        let (clu, facz) := (process pd flag fact_cluster (count) len cs)
        (c :: clu, facz)
      else
        let common := Trie.CountCommon pd.name_list c.1
        let candidate_ratio := ( Nat.toFloat common ) /  S
        let cluster_ratio := ( Nat.toFloat common ) / (Nat.toFloat (Trie.size c.1))
        --dbg_trace s!"Common names : {common} ; candidate ratio : {candidate_ratio} ; cluster ratio : {cluster_ratio}"
        -- v1
        -- if ratio ≥ 0.33
        -- then  let merged_trie := Trie.merge pd.name_list c.1
        --       let clust := pd :: c.2
        --       if ratio ≥ 0.66
        --       then let (clu, facz) := (process pd true fact_cluster cs) ; ((merged_trie, clust) :: clu, facz)
        --       else let (clu, facz) := (process pd flag fact_cluster cs) ; ((merged_trie, clust) :: clu, facz)
        -- else let (clu, facz) := (process pd flag fact_cluster cs) ; (c :: clu, facz)
        -- v2
        if candidate_ratio ≥ 0.7 ∧ cluster_ratio ≥ 0.2
        then  --dbg_trace s!"Merging!"
              let merged_trie := Trie.merge pd.name_list c.1
              let clust := pd :: c.2
              let (clu, facz) := (process pd true fact_cluster (count + 1) len cs)
              ((merged_trie, clust) :: clu, facz)
        else --dbg_trace s!"Skipping"
             let (clu, facz) := (process pd flag fact_cluster (count) len cs)
             (c :: clu, facz)
    else
      --dbg_trace s!"Insertion count above quater length → skipping"
      let (clu, facz) := (process pd true fact_cluster (count) len cs)
      (c :: clu, facz)

def cluster : List gdata → (List (Trie Unit × (List gdata)) × ((List gdata)))
| [] => ([], [])
| pd :: rest =>
    let (sofar_c, sofar_f) := cluster rest
    --dbg_trace s!"\nEntering new process phase with {sofar_c.length}+1 clusters\nFitting {pd.cst_name} with data {Trie.print_keys ⟨#[]⟩ pd.name_list}\n"
    process pd false sofar_f 0 sofar_c.length sofar_c


def phase_two  (clu : List gdata) : (List (Trie Unit × (List gdata))):=
  let inters :=
    match clu with
    | [] => Trie.empty
    | _ => clu.tail.foldl (fun I t => Trie.intersect I t.name_list) clu.head!.name_list
  dbg_trace s!"Intersection of cluster names: {Trie.print_keys ⟨#[]⟩ inters}"
  let rec c :  List gdata → (List (Trie Unit × (List gdata)) × ((List gdata)))
    | [] => ([], [])
    | pd :: rest =>
        let (sofar_c, sofar_f) := c rest
        dbg_trace s!"\nEntering new process phase with {sofar_c.length}+1 clusters\nFitting {pd.cst_name} with data {Trie.print_keys ⟨#[]⟩ pd.name_list}\n"
        process {pd with name_list := Trie.filter pd.name_list inters} false sofar_f 0 sofar_c.length sofar_c

  let (petals, core) := c clu
  (inters, core) :: petals



def phase_two_electric_boogaloo  (clu : (List gdata)) : (List (Trie Unit × (List gdata))):=
  let merge_count_trie :=
    match clu with
    | [] => Trie.empty
    | _ => clu.tail.foldl (fun M t => Trie.merge_count M (Trie.merge_count_initialise t.name_list)) (Trie.merge_count_initialise clu.head!.name_list)
  let core_trie := Trie.cut merge_count_trie 0.5
  let rec c :  List gdata → (List (Trie Unit × (List gdata)) × ((List gdata)))
    | [] => ([], [])
    | pd :: rest =>
        let (sofar_c, sofar_f) := c rest
        --dbg_trace s!"\nEntering new process phase with {sofar_c.length}+1 clusters\nFitting {pd.cst_name} with data {Trie.print_keys ⟨#[]⟩ pd.name_list}\n"
        process {pd with name_list := Trie.filter pd.name_list core_trie} false sofar_f 0 sofar_c.length sofar_c

  let (petals, core) := c clu
  (core_trie, core) :: petals



elab "make_cluster" : command => do
  -- v1
  --let preres := cluster cluster_list
  --let res := (Trie.empty , preres.2) :: preres.1
  -- v2
  dbg_trace s!"Clustering!"
  let (preres, eres) := cluster goal_cluster_list
  dbg_trace s!"Phase 2 !"
  let res := (Trie.empty , eres) :: (List.join (preres.map (fun c => dbg_trace s!"Phase two one cluster {Trie.print_keys ⟨#[]⟩ c.1}" ; phase_two_electric_boogaloo c.2)))
  -- common
  let printit := res.map (fun (t,l) => s!"⟨{print_trie t}, [{String.intercalate "," (l.map (fun p => "GDATA." ++ p.cst_name.toString))}]⟩")
  let (package, cluster_num) := printit.foldl (fun (s,count) d => ((s!"\ndef cluster_{count} : Trie Unit × (List gdata) := " ++ d) :: s, count+1)) ([""],0)
  let cl_L := s!"\ndef g_cl_L : List (Trie Unit × (List gdata)) := [{String.intercalate "," ((List.range printit.length).map (fun n => s!"cluster_{n}"))}]"
              -- else return hmm) ["import Caches.mark2cache_v2\n"]
  let source := "import LeanGrow.Caches.mark1goalCache\nopen Lean Data\n" ++ ((String.join package) ++  cl_L)
  IO.FS.writeFile ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/mark1goalClusters.lean"⟩ (source)

-- produces file that fails to lakebuild even with increased maxHeartbeat XD
-- I used to prenit the whole gdata in teh clusters, instead of mentioning their names
--make_cluster
