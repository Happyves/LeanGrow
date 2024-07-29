
import LeanGrow.Quadtree

import LeanGrow.Caches.mark2clusters_v2
import LeanGrow.Caches.mark1goalClusters


open Lean

#check cluster_list


elab "makeTransitionGraph" : command => do
  let mut inner_graph : QT Nat Nat Nat := QT_initialize 0 cl_L_a.size 0 cl_L_a.size
  let mut bip_graph : QT Nat Nat Nat := QT_initialize 0 cl_L_a.size 0 cl_L_a.size
  let mut icl := 0
  for (_, clustL) in cl_L_a do
    for pd in clustL do
      let mut icr := 0
      for (t,_) in cl_L_a do
        let inter := Trie.CountCommon pd.sink_cst_names t
        if inter ≠ 0 ∨ (Trie.size t == 0)
        then inner_graph := inner_graph.update icl icr (Nat.succ)
        icr := icr+1
      icr := 0
      for (t,_) in g_cl_L_a do
        let inter := Trie.CountCommon pd.goal_cst_names t
        if inter ≠ 0 ∨ (Trie.size t == 0)
        then bip_graph := bip_graph.update icl icr (Nat.succ)
        icr := icr+1
    icl := icl+1
  let source := s!"import LeanGrow.Quadtree\ndef inner_tran_g : QT Nat Nat Nat := {QT.toString instToStringNat.toString instToStringNat.toString instToStringNat.toString inner_graph}\ndef bip_tran_g : QT Nat Nat Nat := {QT.toString instToStringNat.toString instToStringNat.toString instToStringNat.toString bip_graph}"
  IO.FS.writeFile ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/transitionGraphs.lean"⟩ (source)

--makeTransitionGraph -- takes fucking ages, don't know if this is some bug


--#exit

elab "makeTransitionGraph_duh" : command => do
  let mut icl := 1
  let mut toSource := ""
  for (_, clustL) in cl_L_a do
    let mut inner_graph : Array Nat := Array.mkArray ((clustL.length) * (clustL.length)) 0
    let mut bip_graph : Array Nat := Array.mkArray ((clustL.length) * g_cl_L_a.size) 0
    for pd in clustL do
      let mut icr := 1
      for (t,_) in cl_L_a do
        let inter := Trie.CountCommon pd.sink_cst_names t
        if inter ≠ 0 ∨ (Trie.size t == 0)
        then inner_graph := inner_graph.modify ((icl*icr)-1) (· +1)
        icr := icr+1
      icr := 0
      for (t,_) in g_cl_L_a do
        let inter := Trie.CountCommon pd.goal_cst_names t
        if inter ≠ 0 ∨ (Trie.size t == 0)
        then bip_graph := bip_graph.modify ((icl*icr)-1) (· +1)
        icr := icr+1
    toSource := s!"\ndef inner_tran_g_{icl} : Array Nat  := {inner_graph}\ndef bip_tran_g_{icl} : Array Nat := {bip_graph}" ++ toSource
    icl := icl+1
  let source := s!"import LeanGrow.Quadtree" ++ toSource
  IO.FS.writeFile ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/transitionGraphs.lean"⟩ (source)

--makeTransitionGraph_duh
-- the perfromance might be ass because  the parsing causes repeated Array.push ??? Which copies the array ??

#eval cl_L_a.size * cl_L_a.size

--#exit

elab "makeTransitionGraph_hope" : command => do
  let mut inner_graph : Array Nat := Array.mkArray (cl_L_a.size * cl_L_a.size) 0
  let mut bip_graph : Array Nat := Array.mkArray (cl_L_a.size * g_cl_L_a.size) 0
  let mut icl := 1
  for (_, clustL) in cl_L_a do
    for pd in clustL do
      let mut icr := 1
      for (t,_) in cl_L_a do
        let inter := Trie.CountCommon pd.sink_cst_names t
        if inter ≠ 0 ∨ (Trie.size t == 0)
        then inner_graph := inner_graph.modify ((icl*icr)-1) (· +1)
        icr := icr+1
      icr := 0
      for (t,_) in g_cl_L_a do
        let inter := Trie.CountCommon pd.goal_cst_names t
        if inter ≠ 0 ∨ (Trie.size t == 0)
        then bip_graph := bip_graph.modify ((icl*icr)-1) (· +1)
        icr := icr+1
    icl := icl+1
  let source := String.intercalate "," (inner_graph.map instToStringNat.toString).toList
  IO.FS.writeFile ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/transitionGraphs.csv"⟩ (source)

--makeTransitionGraph_hope


partial def parsin (s : String) : Option (List Nat) :=
  let actually := s.data
  let rec loop (l : List Char) : Option (List Nat) :=
    if l = []
    then
      .some []
    else
      let prenum := l.takeWhile (· != ',')
      --dbg_trace "test"
      let rest := l.dropWhile (· != ',')
      let nat? := String.toNat? (String.mk prenum)
      match nat?, loop (rest.tail) with
      | .some n, .some l => .some (n :: l)
      | _, _ => .none
  loop actually



elab "test_csv_parse" : command => do
  let source ← IO.FS.readFile ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/transitionGraphs.csv"⟩
  let out := parsin source
  IO.print out

set_option maxRecDepth 10000

--test_csv_parse


def parsin2 (cached : Nat) : List Char →  Option (List Nat)
| [] => .some [cached]
| c :: rest =>
    match c with
    | '0' => parsin2 (10*cached + 0) rest
    | '1' => parsin2 (10*cached + 1) rest
    | '2' => parsin2 (10*cached + 2) rest
    | '3' => parsin2 (10*cached + 3) rest
    | '4' => parsin2 (10*cached + 4) rest
    | '5' => parsin2 (10*cached + 5) rest
    | '6' => parsin2 (10*cached + 6) rest
    | '7' => parsin2 (10*cached + 7) rest
    | '8' => parsin2 (10*cached + 8) rest
    | '9' => parsin2 (10*cached + 9) rest
    | ',' =>
        match parsin2 0 rest with
        | .some sofar => cached :: sofar
        | .none => .none
    | _ => .none




elab "test_csv_parse2" : command => do
  let source ← IO.FS.readFile ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/transitionGraphs.csv"⟩
  let out := parsin2 0 source.data
  IO.print out

set_option maxRecDepth 10000
set_option maxHeartbeats 0


--test_csv_parse2



-- # The ones that work

elab "makeTransitionGraph_pray" : command => do
  let res := QT_build 0 (cl_L_a.size - 1) 0 (cl_L_a.size - 1)
      (fun x y =>
          let cl := cl_L_a.get! x
          let cr := cl_L_a.get! y
          Id.run do
            let mut out := 0
            for pd in cl.2 do
              if Trie.CountCommon pd.goal_cst_names cr.1 ≠ 0
              then out := out + 1
            return out
          )
      3
  let source := s!"import LeanGrow.Quadtree\n" ++ (String.intercalate "\n" (res.map (fun (n,qt) => s!"def {n} : QT Nat Nat Wrap := {QT.toString instToStringNat.toString instToStringNat.toString ValPost.toStringTrick qt}")))
  IO.FS.writeFile ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/transitionGraphs.lean"⟩ (source)

--makeTransitionGraph_pray


elab "makeProcessedTransitionGraph" : command => do
  let ratio := 0.2
  let mut a_o_as := #[]
  let split_param := 10
  let num_splits := cl_L_a.size / split_param
  for ca in [0:(num_splits)] do
    let mut A := #[]
    for spc in [0:(split_param)] do
      let (_,clu) := cl_L_a.get! (split_param*ca + spc)
      let mut common := (Array.range (cl_L_a.size)).map (fun x => (x,0))
      let mut hits := 0
      for pd in clu do
        for mc in [0:cl_L_a.size] do
          if Trie.CountCommon pd.goal_cst_names (cl_L_a.get! mc).1 ≠ 0
          then common := common.modify mc (fun (x,n) => (x, Nat.succ n)) ; hits := hits + 1
          else continue
      -- take clusters until third of proba distrib is reached
      if hits = 0
      then A := A.push []
      else
        --dbg_trace s!"{common}"
        common := common.qsort (fun (_,v1) (_,v2) => v1 > v2)
        --dbg_trace s!"▸          {((List.range 10).map (common.get!))}"
        let mut S := 0
        let mut s := 0
        for (_,v) in common do
          if (Nat.toFloat s) / (Nat.toFloat hits) ≤ ratio
          then S := S+1 ; s := s + v
          else break
        A := A.push ((List.range S).map (common.get!))
    a_o_as := a_o_as.push A
  -- last bit
  let mut A := #[]
  for spc in [0:(cl_L_a.size  % split_param)] do
    let (_,clu) := cl_L_a.get! (split_param*num_splits + spc)
    let mut common := (Array.range (cl_L_a.size)).map (fun x => (x,0))
    let mut hits := 0
    for pd in clu do
      for mc in [0:cl_L_a.size] do
        if Trie.CountCommon pd.goal_cst_names (cl_L_a.get! mc).1 ≠ 0
        then common := common.modify mc (fun (x,n) => (x, Nat.succ n)) ; hits := hits + 1
        else continue
    if hits = 0
    then A := A.push []
    else
      common := common.qsort (fun (_,v1) (_,v2) => v1 > v2)
      --dbg_trace s!"{((List.range 10).map (common.get!))}"
      let mut S := 0
      let mut s := 0
      for (_,v) in common do
        if (Nat.toFloat s) / (Nat.toFloat hits) ≤ ratio
        then S := S+1 ; s := s + v
        else break
      A := A.push ((List.range S).map (common.get!))
  a_o_as := a_o_as.push A
  -- print
  let mut toSource := []
  let mut co := 0
  for a in a_o_as do
    toSource := s!"\ndef cl_L_a_t_{co} : Array (List (Nat × Nat)) := {a}" :: toSource
    co := co+1
  toSource := toSource.reverse
  let source := String.join toSource
  IO.FS.writeFile ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/ProcessedTransitionGraphs.lean"⟩ (source)

--makeProcessedTransitionGraph

elab "makeProcessedTransitionGraph2" : command => do
  let mut a_o_as := #[]
  let split_param := 10
  let num_splits := cl_L_a.size / split_param
  for ca in [0:(num_splits)] do
    let mut A := #[]
    for spc in [0:(split_param)] do
      let (_,clu) := cl_L_a.get! (split_param*ca + spc)
      let mut common := (Array.range (cl_L_a.size)).map (fun x => (x,0))
      let mut hits := true
      for pd in clu do
        for mc in [0:cl_L_a.size] do
          if Trie.CountCommon pd.goal_cst_names (cl_L_a.get! mc).1 ≠ 0
          then common := common.modify mc (fun (x,n) => (x, Nat.succ n)) ; hits := false
          else continue
      -- take clusters until common-count drops by half
      if hits
      then A := A.push []
      else
        common := common.qsort (fun (_,v1) (_,v2) => v1 > v2)
        let mut S := 0
        let mut s := (common.get! 0).2
        for x in [1 : common.size] do
          let temp := common.get! x
          if temp.2 ≥ (s / 2) ∧ temp.2 ≠ 0
          then S := S+1 ; s := temp.2
          else break
        A := A.push ((List.range S).map (common.get!))
    a_o_as := a_o_as.push A
  -- last bit
  let mut A := #[]
  for spc in [0:(cl_L_a.size  % split_param)] do
    let (_,clu) := cl_L_a.get! (split_param*num_splits + spc)
    let mut common := (Array.range (cl_L_a.size)).map (fun x => (x,0))
    let mut hits := 0
    for pd in clu do
      for mc in [0:cl_L_a.size] do
        if Trie.CountCommon pd.goal_cst_names (cl_L_a.get! mc).1 ≠ 0
        then common := common.modify mc (fun (x,n) => (x, Nat.succ n)) ; hits := hits + 1
        else continue
    if hits = 0
    then A := A.push []
    else
      common := common.qsort (fun (_,v1) (_,v2) => v1 > v2)
      let mut S := 0
      let mut s := (common.get! 0).2
      for x in [1 : common.size] do
        let temp := common.get! x
        if temp.2 ≥ (s / 2) ∧ temp.2 ≠ 0
        then S := S+1 ; s := temp.2
        else break
      A := A.push ((List.range S).map (common.get!))
  a_o_as := a_o_as.push A
  -- print
  let mut toSource := []
  let mut co := 0
  for a in a_o_as do
    toSource := s!"\ndef cl_L_a_t_{co} : Array (List (Nat × Nat)) := {a}" :: toSource
    co := co+1
  toSource := toSource.reverse
  let source := String.join toSource
  IO.FS.writeFile ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/ProcessedTransitionGraphs.lean"⟩ (source)

--makeProcessedTransitionGraph2


elab "makeProcessedTransitionGraphGoals" : command => do
  let mut a_o_as := #[]
  let split_param := 10
  let num_splits := cl_L_a.size / split_param
  for ca in [0:(num_splits)] do
    let mut A := #[]
    for spc in [0:(split_param)] do
      let (_,clu) := cl_L_a.get! (split_param*ca + spc)
      let mut common := (Array.range (g_cl_L_a.size)).map (fun x => (x,0))
      let mut hits := true
      for pd in clu do
        for mc in [0:g_cl_L_a.size] do
          if Trie.CountCommon pd.goal_cst_names (g_cl_L_a.get! mc).1 ≠ 0
          then common := common.modify mc (fun (x,n) => (x, Nat.succ n)) ; hits := false
          else continue
      -- take clusters until common-count drops by half
      if hits
      then A := A.push []
      else
        common := common.qsort (fun (_,v1) (_,v2) => v1 > v2)
        let mut S := 0
        let mut s := (common.get! 0).2
        for x in [1 : common.size] do
          let temp := common.get! x
          if temp.2 ≥ (s / 2) ∧ temp.2 ≠ 0
          then S := S+1 ; s := temp.2
          else break
        A := A.push ((List.range S).map (common.get!))
    a_o_as := a_o_as.push A
  -- last bit
  let mut A := #[]
  for spc in [0:(cl_L_a.size  % split_param)] do
    let (_,clu) := cl_L_a.get! (split_param*num_splits + spc)
    let mut common := (Array.range (g_cl_L_a.size)).map (fun x => (x,0))
    let mut hits := 0
    for pd in clu do
      for mc in [0:g_cl_L_a.size] do
        if Trie.CountCommon pd.goal_cst_names (g_cl_L_a.get! mc).1 ≠ 0
        then common := common.modify mc (fun (x,n) => (x, Nat.succ n)) ; hits := hits + 1
        else continue
    if hits = 0
    then A := A.push []
    else
      common := common.qsort (fun (_,v1) (_,v2) => v1 > v2)
      let mut S := 0
      let mut s := (common.get! 0).2
      for x in [1 : common.size] do
        let temp := common.get! x
        if temp.2 ≥ (s / 2) ∧ temp.2 ≠ 0
        then S := S+1 ; s := temp.2
        else break
      A := A.push ((List.range S).map (common.get!))
  a_o_as := a_o_as.push A
  -- print
  let mut toSource := []
  let mut co := 0
  for a in a_o_as do
    toSource := s!"\ndef g_cl_L_a_t_{co} : Array (List (Nat × Nat)) := {a}" :: toSource
    co := co+1
  toSource := toSource.reverse
  let source := String.join toSource
  IO.FS.writeFile ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/ProcessedTransitionGraphsGolas.lean"⟩ (source)

--makeProcessedTransitionGraphGoals
