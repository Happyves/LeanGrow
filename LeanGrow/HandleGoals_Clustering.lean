
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
      let ratio := ( Nat.toFloat common ) / (min S (Nat.toFloat (Trie.size c.1)))
      -- v1
      -- if ratio ≥ 0.33
      -- then  let merged_trie := Trie.merge pd.name_list c.1
      --       let clust := pd :: c.2
      --       if ratio ≥ 0.66
      --       then let (clu, facz) := (process pd true fact_cluster cs) ; ((merged_trie, clust) :: clu, facz)
      --       else let (clu, facz) := (process pd flag fact_cluster cs) ; ((merged_trie, clust) :: clu, facz)
      -- else let (clu, facz) := (process pd flag fact_cluster cs) ; (c :: clu, facz)
      -- v2
      if ratio ≥ 0.8
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

def phase_two  (clu : List gdata) : (List (Trie Unit × (List gdata))):=
  let inters :=
    match clu with
    | [] => Trie.empty
    | _ => clu.tail.foldl (fun I t => Trie.intersect I t.name_list) clu.head!.name_list

  let rec c :  List gdata → (List (Trie Unit × (List gdata)) × ((List gdata)))
    | [] => ([], [])
    | pd :: rest =>
        let (sofar_c, sofar_f) := c rest
        process {pd with name_list := Trie.filter pd.name_list inters} false sofar_f sofar_c

  let (petals, core) := c clu
  (inters, core) :: petals


elab "make_cluster" : command => do
  -- v1
  --let preres := cluster cluster_list
  --let res := (Trie.empty , preres.2) :: preres.1
  -- v2
  let (preres, eres) := cluster goal_cluster_list
  let res := (Trie.empty , eres) :: (List.join (preres.map (fun c => phase_two c.2)))
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
