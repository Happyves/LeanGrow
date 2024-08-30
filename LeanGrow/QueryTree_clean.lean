

import LeanGrow.QueryTree_idea
import LeanGrow.CExpr
import Mathlib.Data.List.MinMax
import LeanGrow.Caches.Querytree
import LeanGrow.Caches.QuerytreeGoal




open Lean

def preBS.toString_core {α : Type _} (string_alpha : α → String) (string_pointer : Nat → String) : preBS α → String
| .ofVal (a : α) => s!"(BS.ofVal ({string_alpha a}))"
| .ofPoint (p : Nat) => s!"(BS.ofPoint ({string_pointer p}))"

def QueryTree.toString_preBS' (T : QueryTree (preBS α)) (string_alpha : α → String) (string_pointer : Nat → String) : String :=
      QueryTree.toString (preBS.toString_core string_alpha string_pointer) T


partial def QueryTree.deStratify (root? : Bool) : QueryTree (BS α) → (List (QueryTree α))
| .root c => if root? then [.root (c.map (QueryTree.deStratify false)).join] else (c.map (QueryTree.deStratify false)).join
| .node t c => [.node t (c.map (QueryTree.deStratify false)).join]
| .leaf (.ofVal x) => [.leaf x]
| .leaf (.ofPoint p) => QueryTree.deStratify false p


partial def QueryTree.depth : QueryTree α → Nat
| .root c => match List.maximum (c.map QueryTree.depth) with | .some x => x+1 | .none => 1
| .node _ c => match List.maximum (c.map QueryTree.depth) with | .some x => x+1 | .none => 1
| .leaf _ => 0



def QueryTree.join_buggy_leaves_main : List (QueryTree α) → (List α) × List (QueryTree α)
| [] => ([],[])
| x :: l =>
      match x with
      | .node (.leaf .none) [.leaf ( a)] => let (j,o) := QueryTree.join_buggy_leaves_main l ; (a :: j, o)
      | .leaf (a) => let (j,o) := QueryTree.join_buggy_leaves_main l ; (a :: j, o)
      | x =>  let (j,o) := QueryTree.join_buggy_leaves_main l ; (j, x :: o)

partial def QueryTree.getVals (T : QueryTree α) : (List α):=
  match T with
  | .root c => (c.map (QueryTree.getVals)).join
  | .node _ c => (c.map (QueryTree.getVals)).join
  | .leaf (a) => [a]

-- at depth of children
partial def QueryTree.controled_collapse (at_depth : Nat) : QueryTree α → QueryTree (List α)
| .root c =>
    let (j,o) := QueryTree.join_buggy_leaves_main c
    let (y, z) := Id.run do
      let mut cs := []
      let mut ts := []
      for t in o do
        let probe := QueryTree.depth t
        if probe ≤ at_depth
        then
          cs := (QueryTree.getVals t) :: cs
        else
          let τ := QueryTree.controled_collapse at_depth t
          ts := τ :: ts
      return (cs,ts)
    .root ((.leaf ((j :: y)).join) :: z)
| .node nt c =>
    let (j,o) := QueryTree.join_buggy_leaves_main c
    let (y, z) := Id.run do
      let mut cs := []
      let mut ts := []
      for t in o do
        let probe := QueryTree.depth t
        if probe ≤ at_depth
        then
          cs := (QueryTree.getVals t) :: cs
        else
          let τ := QueryTree.controled_collapse at_depth t
          ts := τ :: ts
      return (cs,ts)
    .node nt ((.leaf ((j :: y)).join) :: z)
| .leaf (a) => .leaf ([a])

-- at depth of parents
partial def QueryTree.controled_collapse' (at_depth count : Nat) : QueryTree α → QueryTree (List α)
| .root c =>
    let (j,o) := QueryTree.join_buggy_leaves_main c
    let (y, z) := Id.run do
      let mut cs := []
      let mut ts := []
      for t in o do
        if count ≥ at_depth
        then
          cs := (QueryTree.getVals t) :: cs
        else
          let τ := QueryTree.controled_collapse' at_depth (count + 1) t
          ts := τ :: ts
      return (cs,ts)
    .root ((.leaf ((j :: y)).join) :: z)
| .node nt c =>
    let (j,o) := QueryTree.join_buggy_leaves_main c
    let (y, z) := Id.run do
      let mut cs := []
      let mut ts := []
      for t in o do
        if count ≥ at_depth
        then
          cs := (QueryTree.getVals t) :: cs
        else
          let τ := QueryTree.controled_collapse' at_depth (count + 1) t
          ts := τ :: ts
      return (cs,ts)
    .node nt ((.leaf ((j :: y)).join) :: z)
| .leaf (a) => .leaf ([a])




-- collapses starting from depth `from_depth`, if sub tree has depth less then `at_depth`
partial def QueryTree.controled_collapse'' (at_depth from_depth count : Nat) : QueryTree α → QueryTree (List α)
| .root c =>
    let (j,o) := QueryTree.join_buggy_leaves_main c
    let (y, z) := Id.run do
      let mut cs := []
      let mut ts := []
      for t in o do
        let probe := QueryTree.depth t
        if (count ≥ from_depth) ∧ (probe ≤ at_depth)
        then
          cs := (QueryTree.getVals t) :: cs
        else
          let τ := QueryTree.controled_collapse'' at_depth from_depth (count+1) t
          ts := τ :: ts
      return (cs,ts)
    .root ((.leaf ((j :: y)).join) :: z)
| .node nt c =>
    let (j,o) := QueryTree.join_buggy_leaves_main c
    let (y, z) := Id.run do
      let mut cs := []
      let mut ts := []
      for t in o do
        let probe := QueryTree.depth t
        if (count ≥ from_depth) ∧ (probe ≤ at_depth)
        then
          cs := (QueryTree.getVals t) :: cs
        else
          let τ := QueryTree.controled_collapse'' at_depth from_depth (count+1) t
          ts := τ :: ts
      return (cs,ts)
    .node nt ((.leaf ((j :: y)).join) :: z)
| .leaf (a) => .leaf ([a])



partial def QueryTree.enumVals (count : Nat) : QueryTree α → Nat × QueryTree Nat × List (Nat × α)
| .root c => Id.run do
          let mut no := []
          let mut cs := []
          let mut k := count
          for qt in c do
            let (x,y,z) := QueryTree.enumVals k qt
            cs := z ++ cs
            no := y :: no
            k := x
          return (k, .root no, cs)
| .node nt c => Id.run do
          let mut no := []
          let mut cs := []
          let mut k := count
          for qt in c do
            let (x,y,z) := QueryTree.enumVals k qt
            cs := z ++ cs
            no := y :: no
            k := x
          return (k, .node nt no, cs)
| .leaf x => (count+1, .leaf count, [(count,x)])





elab "make_smooth_clusters_from_querytree_wL" : command => do
  let col := 2
  let .some deT := (QueryTree.deStratify true tha_tree).head? | throwError "aaahhh"
  let CT := QueryTree.controled_collapse col deT
  let (_, LT, clustas) := QueryTree.enumVals 0 CT
  let (_ , sLTs, sLTtop) := QueryTree.stratify 2 2 0 LT
  let mut presource := []
  for (i,c) in clustas do
    presource := s!"\ndef Lsclu_from_qt_{i} : List pdata := [{String.intercalate ", " (c.map (fun x => s!"PDATA.{x.cst_name}"))}]" :: presource
  presource := s!"\ndef Lsclu_from_qt_all : List (Nat × (List pdata)) := [{String.intercalate ", " ((clustas.map Prod.fst).map (fun n => s!"({n},Lsclu_from_qt_{n})"))}]" :: presource
  for (i,t) in sLTs.reverse do
    presource := s!"\ndef lt_{i} : QueryTree (BS (Nat × List pdata)) := {QueryTree.toString_preBS' t (fun n => s!"({n}, Lsclu_from_qt_{n})") (fun n => s!"lt_{n}")}" :: presource
  presource := s!"\ndef LinkTreeTop : QueryTree (BS (Nat × List pdata)) := {QueryTree.toString_preBS' sLTtop (fun n => s!"({n}, Lsclu_from_qt_{n})") (fun n => s!"lt_{n}")}" :: presource
  let source := s!"import LeanGrow.Caches.mark2cache_v2_big\nimport LeanGrow.QueryTree_idea\nopen Lean Data{String.join (presource.reverse)}"
  IO.FS.writeFile ⟨s!"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/QueryTreeSmoothClusters_wL_col{col}.lean"⟩ (source)

--make_smooth_clusters_from_querytree_wL

elab "make_smooth_clusters_from_querytree_wL_g" : command => do
  let col := 2
  let .some deT := (QueryTree.deStratify true g_tha_tree).head? | throwError "aaahhh"
  let CT := QueryTree.controled_collapse col deT
  let (_, LT, clustas) := QueryTree.enumVals 0 CT
  let (_ , sLTs, sLTtop) := QueryTree.stratify 2 2 0 LT
  let mut presource := []
  for (i,c) in clustas do
    presource := s!"\ndef g_Lsclu_from_qt_{i} : List gdata := [{String.intercalate ", " (c.map (fun x => s!"GDATA.{x.cst_name}"))}]" :: presource
  presource := s!"\ndef g_Lsclu_from_qt_all : List (Nat × (List gdata)) := [{String.intercalate ", " ((clustas.map Prod.fst).map (fun n => s!"({n}, g_Lsclu_from_qt_{n})"))}]" :: presource
  for (i,t) in sLTs.reverse do
    presource := s!"\ndef g_lt_{i} : QueryTree (BS (Nat × List gdata)) := {QueryTree.toString_preBS' t (fun n => s!"({n}, g_Lsclu_from_qt_{n})") (fun n => s!"g_lt_{n}")}" :: presource
  presource := s!"\ndef g_LinkTreeTop : QueryTree (BS (Nat × List gdata)) := {QueryTree.toString_preBS' sLTtop (fun n => s!"({n}, g_Lsclu_from_qt_{n})") (fun n => s!"g_lt_{n}")}" :: presource
  let source := s!"import LeanGrow.Caches.mark1goalCache_big\nimport LeanGrow.QueryTree_idea\nopen Lean Data{String.join (presource.reverse)}"
  IO.FS.writeFile ⟨s!"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/QueryTreeSmoothClustersGoal_wL_col{col}.lean"⟩ (source)

--make_smooth_clusters_from_querytree_wL_g



elab "make_huge_clusters_from_querytree_wL" : command => do
  let col := 2
  let .some deT := (QueryTree.deStratify true tha_tree).head? | throwError "aaahhh"
  let (_, LT, clustas) := QueryTree.enumVals 0 deT
  let (_ , sLTs, sLTtop) := QueryTree.stratify 2 2 0 LT
  let mut presource := []
  for (i,c) in clustas do
    presource := s!"\ndef hLsclu_from_qt_{i} : pdata := PDATA.{c.cst_name}" :: presource
  presource := s!"\ndef hLsclu_from_qt_all : List (Nat × pdata) := [{String.intercalate ", " ((clustas.map Prod.fst).map (fun n => s!"({n},hLsclu_from_qt_{n})"))}]" :: presource
  for (i,t) in sLTs.reverse do
    presource := s!"\ndef hlt_{i} : QueryTree (BS (Nat × pdata)) := {QueryTree.toString_preBS' t (fun n => s!"({n}, hLsclu_from_qt_{n})") (fun n => s!"hlt_{n}")}" :: presource
  presource := s!"\ndef hLinkTreeTop : QueryTree (BS (Nat × pdata)) := {QueryTree.toString_preBS' sLTtop (fun n => s!"({n}, hLsclu_from_qt_{n})") (fun n => s!"hlt_{n}")}" :: presource
  let source := s!"import LeanGrow.Caches.mark2cache_v2_big\nimport LeanGrow.QueryTree_idea\nopen Lean Data{String.join (presource.reverse)}"
  IO.FS.writeFile ⟨s!"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/QueryTreeSmoothClustersHuge_wL_col{col}.lean"⟩ (source)

--make_huge_clusters_from_querytree_wL

elab "make_huge_clusters_from_querytree_wL_g" : command => do
  let col := 2
  let .some deT := (QueryTree.deStratify true g_tha_tree).head? | throwError "aaahhh"
  let (_, LT, clustas) := QueryTree.enumVals 0 deT
  let (_ , sLTs, sLTtop) := QueryTree.stratify 2 2 0 LT
  let mut presource := []
  for (i,c) in clustas do
    presource := s!"\ndef g_hLsclu_from_qt_{i} : gdata := GDATA.{c.cst_name}" :: presource
  presource := s!"\ndef g_hLsclu_from_qt_all : List (Nat × gdata) := [{String.intercalate ", " ((clustas.map Prod.fst).map (fun n => s!"({n}, g_hLsclu_from_qt_{n})"))}]" :: presource
  for (i,t) in sLTs.reverse do
    presource := s!"\ndef g_hlt_{i} : QueryTree (BS (Nat × gdata)) := {QueryTree.toString_preBS' t (fun n => s!"({n}, g_hLsclu_from_qt_{n})") (fun n => s!"g_hlt_{n}")}" :: presource
  presource := s!"\ndef g_hLinkTreeTop : QueryTree (BS (Nat × gdata)) := {QueryTree.toString_preBS' sLTtop (fun n => s!"({n}, g_hLsclu_from_qt_{n})") (fun n => s!"g_hlt_{n}")}" :: presource
  let source := s!"import LeanGrow.Caches.mark1goalCache_big\nimport LeanGrow.QueryTree_idea\nopen Lean Data{String.join (presource.reverse)}"
  IO.FS.writeFile ⟨s!"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/QueryTreeSmoothClustersHuge_g_wL_col{col}.lean"⟩ (source)

--make_huge_clusters_from_querytree_wL_g

#exit

elab "make_smooth_clusters_from_querytree_wL" : command => do
  let from_col := 1
  let at_col := 1
  let .some deT := (QueryTree.deStratify true tha_tree).head? | throwError "aaahhh"
  let CT := QueryTree.controled_collapse'' at_col from_col 0 deT
  let (_, LT, clustas) := QueryTree.enumVals 0 CT
  let (_ , sLTs, sLTtop) := QueryTree.stratify 2 2 0 LT
  let mut presource := []
  for (i,c) in clustas do
    presource := s!"\ndef Lsclu_from_qt_{i} : List pdata := [{String.intercalate ", " (c.map (fun x => s!"PDATA.{x.cst_name}"))}]" :: presource
  presource := s!"\ndef Lsclu_from_qt_all : List (Nat × (List pdata)) := [{String.intercalate ", " ((clustas.map Prod.fst).map (fun n => s!"({n},Lsclu_from_qt_{n})"))}]" :: presource
  for (i,t) in sLTs.reverse do
    presource := s!"\ndef lt_{i} : QueryTree (BS (Nat × List pdata)) := {QueryTree.toString_preBS' t (fun n => s!"({n}, Lsclu_from_qt_{n})") (fun n => s!"lt_{n}")}" :: presource
  presource := s!"\ndef LinkTreeTop : QueryTree (BS (Nat × List pdata)) := {QueryTree.toString_preBS' sLTtop (fun n => s!"({n}, Lsclu_from_qt_{n})") (fun n => s!"lt_{n}")}" :: presource
  let source := s!"import LeanGrow.Caches.mark2cache_v2_big\nimport LeanGrow.QueryTree_idea\nopen Lean Data{String.join (presource.reverse)}"
  IO.FS.writeFile ⟨s!"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/QueryTreeSmoothClusters_wL_col_{at_col}_{from_col}.lean"⟩ (source)

--make_smooth_clusters_from_querytree_wL

elab "make_smooth_clusters_from_querytree_wL_g" : command => do
  let from_col := 1
  let at_col := 1
  let .some deT := (QueryTree.deStratify true g_tha_tree).head? | throwError "aaahhh"
  let CT := QueryTree.controled_collapse'' at_col from_col 0 deT
  let (_, LT, clustas) := QueryTree.enumVals 0 CT
  let (_ , sLTs, sLTtop) := QueryTree.stratify 2 2 0 LT
  let mut presource := []
  for (i,c) in clustas do
    presource := s!"\ndef g_Lsclu_from_qt_{i} : List gdata := [{String.intercalate ", " (c.map (fun x => s!"GDATA.{x.cst_name}"))}]" :: presource
  presource := s!"\ndef g_Lsclu_from_qt_all : List (Nat × (List gdata)) := [{String.intercalate ", " ((clustas.map Prod.fst).map (fun n => s!"({n}, g_Lsclu_from_qt_{n})"))}]" :: presource
  for (i,t) in sLTs.reverse do
    presource := s!"\ndef g_lt_{i} : QueryTree (BS (Nat × List gdata)) := {QueryTree.toString_preBS' t (fun n => s!"({n}, g_Lsclu_from_qt_{n})") (fun n => s!"g_lt_{n}")}" :: presource
  presource := s!"\ndef g_LinkTreeTop : QueryTree (BS (Nat × List gdata)) := {QueryTree.toString_preBS' sLTtop (fun n => s!"({n}, g_Lsclu_from_qt_{n})") (fun n => s!"g_lt_{n}")}" :: presource
  let source := s!"import LeanGrow.Caches.mark1goalCache_big\nimport LeanGrow.QueryTree_idea\nopen Lean Data{String.join (presource.reverse)}"
  IO.FS.writeFile ⟨s!"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/QueryTreeSmoothClustersGoal_wL_col_{at_col}_{from_col}.lean"⟩ (source)

--make_smooth_clusters_from_querytree_wL_g
