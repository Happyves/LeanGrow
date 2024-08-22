
import LeanGrow.QueryTree_idea
import LeanGrow.Caches.Querytree
import LeanGrow.CExpr

open Lean Data Elab Tactic Meta


-- # Query full tree from Ltx

partial def QueryTree.query (Q : Trie Unit) (T : QueryTree (BS α)) : List α :=
  match T with
  | .root c => (c.map (QueryTree.query Q)).join
  | .node t c => if Trie.CountCommon t Q = Trie.size t then (c.map (QueryTree.query Q)).join else []
  | .leaf (.ofVal a) => [a]
  | .leaf (.ofPoint t) => QueryTree.query Q t

elab "testing_queries" : tactic => withMainContext do
  let env ← getEnv
  let ltx ← getLCtx
  let ref ← getRef
  let mut names := []
  for d in ltx.decls do
    match d with
    | .none => pure ()
    | .some D => names := ((Expr.getConstNames D.type).map Name.toString) ++ names
  let res := QueryTree.query (SortedTrieFormList' names) tha_tree
  for r in res do
    let ty := (env.constants.find! r.cst_name).type
    logInfoAt ref s!"\nSuggestion {r.cst_name}: {← ppExpr ty}"


example (l : List ℕ) (a : ℕ) (h : a ∈ l) : True :=
  by
  --testing_queries
  trivial

-- found
#check List.length_erase_add_one
#check List.getElem?_indexOf
-- not found!
#check List.insert_pos
-- may be the issue of Type/Sort in names ?!?!?



example (l L : List ℕ) (h : 0 < l.length) : True :=
  by
  --testing_queries
  trivial

-- foudn
#check List.ne_nil_of_length_pos


example {α : Type u} (l₁ : List α) {l₂ : List α} (h : l₁ ≠ [])  : True :=
  by
  --testing_queries
  trivial

-- found
#check List.head?_append_of_ne_nil


-- # Cluster from full tree



partial def QueryTree.getVals (T : QueryTree (BS α)) : (List α):=
  match T with
  | .root c => (c.map (QueryTree.getVals)).join
  | .node _ c => (c.map (QueryTree.getVals)).join
  | .leaf (.ofPoint P) => QueryTree.getVals P
  | .leaf (.ofVal a) => [a]



partial def QueryTree.collapse (countdown : Nat) (T : QueryTree (BS α)) : QueryTree (BS (List α)) :=
  match T with
  | .root c => .root (c.map (QueryTree.collapse (countdown - 1)))
  | .node t c =>
      if countdown = 0
      then .leaf (.ofVal (c.map (QueryTree.getVals)).join)
      else .node t (c.map (QueryTree.collapse (countdown - 1)))
  | .leaf (.ofPoint P) => (QueryTree.collapse (countdown - 1)) P
  | .leaf (.ofVal a) => .leaf (.ofVal [a])


elab "make_clusters_from_querytree" : command => do
  let clustas := QueryTree.getVals (QueryTree.collapse 3 tha_tree)
  let mut presource := []
  let mut i := 0
  for c in clustas do
    presource := s!"\ndef clu_from_qt_{i} : List pdata := [{String.intercalate ", " (c.map (fun x => s!"PDATA.{x.cst_name}"))}]" :: presource
    i := i+1
  let source := s!"import LeanGrow.Caches.mark2cache_v2_big\nopen Lean Data{String.join presource}\ndef clu_from_qt_all : List (List pdata) := [{String.intercalate ", " ((List.range i).map (fun n => s!"clu_from_qt_{n}"))}]"
  IO.FS.writeFile ⟨s!"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/QueryTreeClusters.lean"⟩ (source)


--make_clusters_from_querytree
-- too many one-element-clusters ...


partial def QueryTree.depth : QueryTree (BS α) → Nat
| .root c => match List.maximum (c.map QueryTree.depth) with | .some x => x+1 | .none => 1
| .node _ c => match List.maximum (c.map QueryTree.depth) with | .some x => x+1 | .none => 1
| .leaf (.ofPoint P) => QueryTree.depth P
| .leaf (.ofVal _) => 0


def QueryTree.has_only_leaves : List (QueryTree α) → Bool
| [] => true
| x :: l =>
      match x with
      | .leaf _ => QueryTree.has_only_leaves l
      | .node (.leaf .none) _ => QueryTree.has_only_leaves l -- don't know if necessary...
      | _ => false


def QueryTree.join_leaves_main : List (QueryTree (BS α)) → (List α) × List (QueryTree (BS α))
| [] => ([],[])
| x :: l =>
      match x with
      | .leaf (.ofVal a) => let (j,o) := QueryTree.join_leaves_main l ; (a :: j, o)
      | x =>  let (j,o) := QueryTree.join_leaves_main l ; (j, x :: o)

-- should fix this at some point...
def QueryTree.join_buggy_leaves_main : List (QueryTree (BS α)) → (List α) × List (QueryTree (BS α))
| [] => ([],[])
| x :: l =>
      match x with
      | .node (.leaf .none) [.leaf (.ofVal a)] => let (j,o) := QueryTree.join_buggy_leaves_main l ; (a :: j, o)
      | .leaf (.ofVal a) => let (j,o) := QueryTree.join_buggy_leaves_main l ; (a :: j, o)
      | x =>  let (j,o) := QueryTree.join_buggy_leaves_main l ; (j, x :: o)


-- my fucking god. TODO: make sense of this absloute mess
partial def QueryTree.getVals_withBrain (f : List α → β) (T : QueryTree (BS (α))) : (List β):=
  match T with
  | .root c =>
        let (j,o) := QueryTree.join_buggy_leaves_main c
        --dbg_trace s!"\n\nRoot with children:\n{c.map (QueryTree.visualize 0)}\nExtracted: {j.map help}\nProceed on:{o.map (QueryTree.visualize 0)}"
        (f j) :: (o.map (QueryTree.getVals_withBrain f)).join
  | .node _ c =>
        let (j,o) := QueryTree.join_buggy_leaves_main c
        --dbg_trace s!"\n\nNode with children:\n{c.map (QueryTree.visualize 0)}\nExtracted: {j.map help}\nProceed on:{o.map (QueryTree.visualize 0)}"
        (f j) :: (o.map (QueryTree.getVals_withBrain f)).join
  | .leaf (.ofPoint P) => QueryTree.getVals_withBrain f P
  | .leaf (.ofVal a) => [f [a]]

--#exit


partial def QueryTree.controled_collapse (at_depth : Nat) : QueryTree (BS α) → QueryTree (BS (List α))
| .root c =>
    let (j,o) := QueryTree.join_buggy_leaves_main c
    .root (.leaf (.ofVal j) :: (o.map (QueryTree.controled_collapse at_depth)))
| .node t c =>
    let (j,o) := QueryTree.join_buggy_leaves_main c
    Id.run do
      let mut nc := []
      for chi in o do
        let probe := QueryTree.depth chi
        if probe ≥ at_depth
        then nc := (QueryTree.leaf (BS.ofVal (QueryTree.getVals chi))) :: nc
        else nc := (QueryTree.controled_collapse at_depth chi) :: nc
      return .node t (.leaf (.ofVal j) :: nc)
| .leaf (.ofPoint P) =>
      -- this part needs deep fixing
      let hmm := QueryTree.controled_collapse at_depth P
      -- doesn't even fix the problem
      match hmm with
      | .root c =>
          let (j,o) := QueryTree.join_buggy_leaves_main c
          .root (.leaf (.ofVal j.join) :: o )
      | .node t c =>
          let (j,o) := QueryTree.join_buggy_leaves_main c
          .node t (.leaf (.ofVal j.join) :: o )
      | .leaf x => .leaf x
| .leaf (.ofVal a) => .leaf (.ofVal [a])


elab "make_smooth_clusters_from_querytree" : command => do
  let clustas := QueryTree.getVals_withBrain List.join (QueryTree.controled_collapse 0 tha_tree)
  let mut presource := []
  let mut i := 0
  for c in clustas do
    presource := s!"\ndef sclu_from_qt_{i} : List pdata := [{String.intercalate ", " (c.map (fun x => s!"PDATA.{x.cst_name}"))}]" :: presource
    i := i+1
  let source := s!"import LeanGrow.Caches.mark2cache_v2_big\nopen Lean Data{String.join presource}\ndef sclu_from_qt_all : List (List pdata) := [{String.intercalate ", " ((List.range i).map (fun n => s!"sclu_from_qt_{n}"))}]"
  IO.FS.writeFile ⟨s!"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/QueryTreeSmoothClusters.lean"⟩ (source)

--make_smooth_clusters_from_querytree

#eval Trie.print_keys ⟨#[]⟩ PDATA.List.count_join'.sink_cst_names

--(fun v => s!"[{String.intercalate ", " (v.map (fun x => Name.toString x.cst_name))}]")



partial def QueryTree.visualizeM (count : Nat) : QueryTree (BS (List pdata)) → String
| .root c => s!"Root\n ({String.intercalate "\n" (c.map (QueryTree.visualizeM 1))})"
| .node (q : Trie Unit) c => (String.replicate count ' ') ++ s!"Node ({Trie.print_keys ⟨#[]⟩ q})\n{(String.replicate count ' ')}({String.intercalate "\n" (c.map (QueryTree.visualizeM (count + 3)))})"
| .leaf (.ofVal v) => (String.replicate count ' ') ++ s!"Leaf [{String.intercalate ", " (v.map (fun x => Name.toString x.cst_name))}]"
| .leaf (.ofPoint p) => s!"POINT {QueryTree.visualizeM (count + 1) p}"

--#exit

#eval ((QueryTree.visualizeM 0 (QueryTree.controled_collapse 0 tha_tree) )).toFormat





#check List.Forall₂

-- # Query collapsed tree from Ltx
