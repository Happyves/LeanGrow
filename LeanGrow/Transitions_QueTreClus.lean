
import LeanGrow.Caches.QueryTreeSmoothClusters_wL_col2
import LeanGrow.Caches.QueryTreeSmoothClustersGoal_wL_col0
import LeanGrow.QueryTree_Cluster_Query
import LeanGrow.Caches.SmolTransitionGraphs


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
