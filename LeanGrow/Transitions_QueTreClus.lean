
import LeanGrow.Caches.QueryTreeSmoothClusters_wL_col2
import LeanGrow.Caches.QueryTreeSmoothClustersGoal_wL_col0
import LeanGrow.QueryTree_Cluster_Query
import LeanGrow.Caches.SmolTransitionGraphs
import LeanGrow.Caches.LargeTransitionGraphs

open Lean Data

#check RBNode

def RBNode.update {β : Type v} (cmp : α → α → Ordering) (f : β → β)  : RBNode α (fun _ => β) → α → RBNode α (fun _ => β)
  | .leaf,             _ => .leaf
  | .node z a ky vy b, x =>
    match cmp x ky with
    | Ordering.lt => RBNode.update cmp f a x
    | Ordering.gt => RBNode.update cmp f b x
    | Ordering.eq => .node z a ky (f vy) b


def Clus_Nei_inner (clus : List pdata) : RBNode Nat (fun _ => Nat) :=
  match clus with
  | [] => .leaf
  | d :: ds =>
      let nei := QueryTree.query d.goal_cst_names Lsclu_from_qt_all
      Id.run do
        let mut rbn := Clus_Nei_inner ds
        for (n,_) in nei do
          rbn := RBNode.update instOrdNat.compare Nat.succ rbn n
        return rbn


def Clus_Nei_outer (clus : List pdata) : RBNode Nat (fun _ => Nat) :=
  match clus with
  | [] => .leaf
  | d :: ds =>
      let nei := QueryTree.query d.goal_cst_names g_Lsclu_from_qt_all
      Id.run do
        let mut rbn := Clus_Nei_outer ds
        for (n,_) in nei do
          rbn := RBNode.update instOrdNat.compare Nat.succ rbn n
        return rbn


partial def QueryTree.map (f : α → β) : QueryTree α → QueryTree β
| .root c => .root (c.map (QueryTree.map f))
| .node t c => .node t (c.map (QueryTree.map f))
| .leaf x => .leaf (f x)

partial def QueryTree.mapBS (f : α → β) : QueryTree (BS α) → QueryTree (BS β)
| .root c => .root (c.map (QueryTree.mapBS f))
| .node t c => .node t (c.map (QueryTree.mapBS f))
| .leaf (.ofVal x) => .leaf (.ofVal (f x))
| .leaf (.ofPoint p) => .leaf (.ofPoint (QueryTree.mapBS f p))


def RBColor.toString : RBColor → String
| .red => "RBColor.red"
| .black => "RBColor.black"

def RBNode.toString (as : α → String)  (bs : β → String) : RBNode α (fun _ => β) → String
| .leaf => "RBNode.leaf"
| .node  (color : RBColor) (lchild : RBNode α (fun _ => β)) (key : α) (val : β) (rchild : RBNode α (fun _ => β)) =>
      s!"RBNode.node {RBColor.toString color} ({RBNode.toString as bs lchild}) ({as key}) ({bs val}) ({RBNode.toString as bs rchild})"

def BS.toString_trick_more : BS (ℕ × RBNode ℕ (fun _ ↦ ℕ)) → String
| .ofVal (n,a) => s!"(BS.ofVal ({n}, {RBNode.toString (fun x => s!"{x}") (fun x => s!"{x}") a}))"
| .ofPoint (_) => s!"FAIL" -- we expect to run this on the link tree, where there shoudl't be pointer leafs anymore, as we expect it to be small...



elab "make_smol_transition_graphs" : command => do
  let inner := QueryTree.mapBS (fun (n,l) => (n, Clus_Nei_inner l)) Lsclu_from_qt_all
  let outer := QueryTree.mapBS (fun (n,l) => (n, Clus_Nei_outer l)) Lsclu_from_qt_all
  let pti := QueryTree.toString BS.toString_trick_more inner
  let pto := QueryTree.toString BS.toString_trick_more outer
  let source := s!"\nimport LeanGrow.QueryTree_idea\nopen Lean Data\ndef inner_trans : QueryTree (BS (Nat × (RBNode ℕ (fun _ ↦ ℕ)))) := {pti}\ndef outer_trans : QueryTree (BS (Nat × (RBNode ℕ (fun _ ↦ ℕ)))) := {pto}"
  IO.FS.writeFile ⟨s!"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/SmolTransitionGraphs.lean"⟩ (source)

--make_smol_transition_graphs


def Clus_Nei_inner_large (clus : List pdata) : RBNode Nat (fun _ => Nat) :=
  match clus with
  | [] => .leaf
  | d :: ds => Id.run do
      let mut rbn := Clus_Nei_inner_large ds
      for (n,c) in sclu_from_qt_all do
        let mut hits := 0
        for pd in c do
          if Trie.CountCommon pd.sink_cst_names d.goal_cst_names ≠ 0 then hits := hits +1
        rbn := RBNode.update instOrdNat.compare (· + hits) rbn n
      return rbn

def Clus_Nei_outer_large (clus : List pdata) : RBNode Nat (fun _ => Nat) :=
  match clus with
  | [] => .leaf
  | d :: ds => Id.run do
      let mut rbn := Clus_Nei_outer_large ds
      for (n,c) in g_sclu_from_qt_all do
        let mut hits := 0
        for pd in c do
          if Trie.CountCommon pd.name_list d.goal_cst_names ≠ 0 then hits := hits +1
        rbn := RBNode.update instOrdNat.compare (· + hits) rbn n
      return rbn

elab "make_large_transition_graphs" : command => do
  let inner := QueryTree.mapBS (fun (n,l) => (n, Clus_Nei_inner_large l)) Lsclu_from_qt_all
  let outer := QueryTree.mapBS (fun (n,l) => (n, Clus_Nei_outer_large l)) Lsclu_from_qt_all
  let pti := QueryTree.toString BS.toString_trick_more inner
  let pto := QueryTree.toString BS.toString_trick_more outer
  let source := s!"\nimport LeanGrow.QueryTree_idea\nopen Lean Data\ndef inner_trans_large : QueryTree (BS (Nat × (RBNode ℕ (fun _ ↦ ℕ)))) := {pti}\ndef outer_trans_large : QueryTree (BS (Nat × (RBNode ℕ (fun _ ↦ ℕ)))) := {pto}"
  IO.FS.writeFile ⟨s!"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/LargeTransitionGraphs.lean"⟩ (source)

--make_large_transition_graphs
-- 5 to 8 min

def getTotalWeight : RBNode ℕ (fun _ ↦ ℕ) → Nat :=
  RBNode.fold (fun sofar _ v => sofar + v) 0


def RBNode.upsert {β : Type v} (cmp : α → α → Ordering) (f : β → β) (val : β) : RBNode α (fun _ => β) → α → RBNode α (fun _ => β) :=
  fun t k =>
    match t.find cmp k with
    | .some _ => RBNode.update cmp f t k
    | .none => RBNode.insert cmp t k val


-- computes total weights along all walks
def n_step_closure_rbt (N : Nat) (inner outer : List (Nat × (RBNode ℕ (fun _ ↦ ℕ)))) (key : Nat) : Option (RBNode ℕ (fun _ ↦ ℕ)) :=
  match N with
  | 0 => Prod.snd <$> (outer.find? (Prod.fst · = key))
  | n+1 => Id.run do
      let .some nei := Prod.snd <$> inner.find? (Prod.fst · = key) | return .none
      let res := RBNode.fold
          (fun sofar k v => Id.run do
              let .some sofar' := sofar | return .none
              let .some fromhere := Id.run do
                let .some clos := n_step_closure_rbt n inner outer k | return Option.none
                return .some (RBNode.map (fun _ x => x+v) clos) | return Option.none
              return .some (RBNode.fold (fun S K V => RBNode.upsert instOrdNat.compare (fun x => x + V) V S K) sofar' fromhere)
              )
          (Option.some RBNode.leaf) nei
      return res


def RBNode.fromList (l : List (Nat × Nat)) : RBNode ℕ (fun _ ↦ ℕ) :=
  l.foldl (fun s (k,v) => RBNode.insert instOrdNat.compare s k v ) RBNode.leaf

-- unit edge wuit four-cycle
def C4 : List (Nat × (RBNode ℕ (fun _ ↦ ℕ))) :=
  [(0, RBNode.fromList [(1,1), (3,1)]), (1, RBNode.fromList [(0,1), (2,1)]), (2, RBNode.fromList [(1,1), (3,1)]), (3, RBNode.fromList [(0,1), (2,1)]) ]

#eval do
  let .some res := n_step_closure_rbt 1 C4 C4 0 | IO.println "aaahh"
  IO.println (RBNode.toString (fun x => s!"{x}") (fun x => s!"{x}") res)

#eval do
  let .some res := n_step_closure_rbt 1 C4 C4 1 | IO.println "aaahh"
  IO.println (RBNode.toString (fun x => s!"{x}") (fun x => s!"{x}") res)

#eval do
  let .some res := n_step_closure_rbt 1 C4 C4 2 | IO.println "aaahh"
  IO.println (RBNode.toString (fun x => s!"{x}") (fun x => s!"{x}") res)


#exit

/-- requires no BEq on α-/
def List.hasNone? : List (Option α) → Bool
| [] => false
| x :: xs =>
    match x with
    | .none => true
    | _ => xs.hasNone?

partial def QueryTree.mapBS_Opt (f : α → Option β) : QueryTree (BS α) → Option (QueryTree (BS β))
| .root c =>
    let cn := (c.map (QueryTree.mapBS_Opt f))
    if cn.hasNone? then .none else .some (.root (cn.reduceOption))
| .node t c =>
    let cn := (c.map (QueryTree.mapBS_Opt f))
    if cn.hasNone? then .none else .some (.node t (cn.reduceOption))
| .leaf (.ofVal x) =>
    match f x with
    | .some fx => .some (.leaf (.ofVal (fx)))
    | _ => .none
| .leaf (.ofPoint p) =>
    match QueryTree.mapBS_Opt f p with
    | .some P => .some (.leaf (.ofPoint P))
    | _ => .none


def n_step_closure (N : Nat) (inner outer : QueryTree (BS (Nat × (RBNode ℕ (fun _ ↦ ℕ))))) : Option (QueryTree (BS (Nat × (RBNode ℕ (fun _ ↦ ℕ))))) :=
  let inner' := QueryTree.getVals inner
  let outer' := QueryTree.getVals outer
  QueryTree.mapBS_Opt (fun (k,_) => (k, · ) <$> n_step_closure_rbt N inner' outer' k) inner


elab "make_smol_transition_graph_closure" : command => do
  let clos_step := 1
  let .some res := n_step_closure clos_step inner_trans outer_trans | throwError "Fail :<"
  let source := s!"\nimport LeanGrow.QueryTree_idea\nopen Lean Data\ndef smol_closure : QueryTree (BS (Nat × (RBNode ℕ (fun _ ↦ ℕ)))) := {QueryTree.toString BS.toString_trick_more res}"
  IO.FS.writeFile ⟨s!"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/SmolTransitionGraphClosure_clos_{clos_step}.lean"⟩ (source)

--make_smol_transition_graph_closure

elab "make_large_transition_graph_closure" : command => do
  let clos_step := 2
  let .some res := n_step_closure clos_step inner_trans_large outer_trans_large | throwError "Fail :<"
  let source := s!"\nimport LeanGrow.QueryTree_idea\nopen Lean Data\ndef smol_closure : QueryTree (BS (Nat × (RBNode ℕ (fun _ ↦ ℕ)))) := {QueryTree.toString BS.toString_trick_more res}"
  IO.FS.writeFile ⟨s!"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/LargeTransitionGraphClosure_clos_{clos_step}.lean"⟩ (source)

--make_large_transition_graph_closure
