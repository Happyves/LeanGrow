
import LeanGrow.Quadtree

import LeanGrow.Caches.mark2clusters_v2
import LeanGrow.Caches.mark1goalClusters


open Lean

#check cluster_list


elab "makeTransitionGraph" : command => do
  let mut inner_graph : QT Nat Nat Nat := QT.nil
  let mut bip_graph : QT Nat Nat Nat := QT.nil
  let mut icl := 0
  for (_, clustL) in cl_L_a do
    for pd in clustL do
      let mut icr := 0
      for (t,_) in cl_L_a do
        let inter := Trie.CountCommon pd.sink_cst_names t
        if inter ≠ 0 ∨ (Trie.size t == 0)
        then inner_graph := inner_graph.upsert icl icr (fun x => match x with | .none => 1 | .some y => y+1)
        icr := icr+1
      icr := 0
      for (t,_) in g_cl_L_a do
        let inter := Trie.CountCommon pd.goal_cst_names t
        if inter ≠ 0 ∨ (Trie.size t == 0)
        then bip_graph := bip_graph.upsert icl icr (fun x => match x with | .none => 1 | .some y => y+1)
        icr := icr+1
    icl := icl+1
  let source := s!"import LeanGrow.Quadtree\ndef inner_tran_g : QT Nat Nat Nat := {QT.toString instToStringNat.toString instToStringNat.toString instToStringNat.toString inner_graph}\ndef bip_tran_g : QT Nat Nat Nat := {QT.toString instToStringNat.toString instToStringNat.toString instToStringNat.toString bip_graph}"
  IO.FS.writeFile ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/transitionGraphs.lean"⟩ (source)

--makeTransitionGraph

elab "makeTransitionGraph_duh" : command => do
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
  let source := s!"import LeanGrow.Quadtree\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000\ndef inner_tran_g : Array Nat  := {inner_graph}\ndef bip_tran_g : Array Nat := {bip_graph}"
  IO.FS.writeFile ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/transitionGraphs.lean"⟩ (source)

--makeTransitionGraph_duh

#eval cl_L_a.size * cl_L_a.size


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
