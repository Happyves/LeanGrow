
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
        dbg_trace s!"{common}"
        common := common.qsort (fun (_,v1) (_,v2) => v1 ≥ v2)
        dbg_trace s!"▸          {((List.range 10).map (common.get!))}"
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
      common := common.qsort (fun (_,v1) (_,v2) => v1 ≥ v2)
      dbg_trace s!"{((List.range 10).map (common.get!))}"
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

#eval cl_L_a.size

#eval Array.qsort #[(1,0),(2,2),(3,1),(4,0),(4,4),(5,5),(6,0),(7,10),(8,70),(9,0),(10,3)] (fun (_,v1) (_,v2) => v1 ≥ v2)

def testin := #[(0, 0), (1, 2), (2, 0), (3, 0), (4, 2), (5, 2), (6, 0), (7, 0), (8, 0), (9, 0), (10, 0), (11, 0), (12, 2), (13, 0), (14, 0), (15, 0), (16, 0), (17, 0), (18, 0), (19, 0), (20, 2), (21, 0), (22, 0), (23, 2), (24, 0), (25, 0), (26, 0), (27, 2), (28, 0), (29, 2), (30, 0), (31, 0), (32, 2), (33, 0), (34, 0), (35, 0), (36, 0), (37, 0), (38, 0), (39, 0), (40, 0), (41, 0), (42, 0), (43, 0), (44, 0), (45, 0), (46, 2), (47, 0), (48, 0), (49, 0), (50, 0), (51, 0), (52, 0), (53, 2), (54, 0), (55, 0), (56, 2), (57, 2), (58, 0), (59, 0), (60, 0), (61, 0), (62, 0), (63, 2), (64, 0), (65, 0), (66, 0), (67, 0), (68, 0), (69, 0), (70, 0), (71, 0), (72, 2), (73, 0), (74, 0), (75, 0), (76, 2), (77, 2), (78, 0), (79, 0), (80, 2), (81, 0), (82, 2), (83, 0), (84, 0), (85, 0), (86, 0), (87, 0), (88, 2), (89, 0), (90, 2), (91, 0), (92, 0), (93, 0), (94, 2), (95, 0), (96, 0), (97, 0), (98, 0), (99, 0), (100, 2), (101, 0), (102, 2), (103, 2), (104, 0), (105, 0), (106, 0), (107, 0), (108, 0), (109, 0), (110, 0), (111, 2), (112, 0), (113, 0), (114, 0), (115, 0), (116, 0), (117, 0), (118, 0), (119, 0), (120, 0), (121, 0), (122, 0), (123, 0), (124, 0), (125, 0), (126, 2), (127, 0), (128, 0), (129, 2), (130, 2), (131, 2), (132, 2), (133, 2), (134, 2), (135, 0), (136, 0), (137, 0), (138, 0), (139, 0), (140, 0), (141, 0), (142, 0), (143, 0), (144, 0), (145, 0), (146, 0), (147, 0), (148, 0), (149, 0), (150, 2), (151, 2), (152, 0), (153, 0), (154, 0), (155, 0), (156, 0), (157, 0), (158, 0), (159, 0), (160, 0), (161, 0), (162, 0), (163, 0), (164, 0), (165, 0), (166, 0)]

#eval testin.size

#eval Array.qsort testin (fun (_,v1) (_,v2) => v1 ≥ v2)
