
import LeanGrow.F.Utils.DAG.Types
import LeanGrow.F.Utils.Array

-- # labelDataList

def pDAG.labelDataList (d : pDAG α β) : List (β × α) :=
  d.map (fun ⟨n, D, _⟩ => (n,D))

def DAG.labelDataList (d : DAG α β) : List (β × α) :=
  d.map (fun ⟨n, D, _, _⟩ => (n,D) )

def sDAG.labelDataArray (α β : Type _) {store : Type _ → Type _} [ToIdx β store]
  [Repr (store β)] [Inhabited (store β)] [BEq (store β)] (d : sDAG α β store) : Array β :=
  d.idx_to_label




-- # Data Lists

def pDAG.dataParentsList_ofLabel [BEq β] (lab : β) : pDAG α β → Option (α × (List β))
| [] => .none
| x :: l => if x.label == lab then .some (x.data, x.parents) else (pDAG.dataParentsList_ofLabel lab l)


def DAG.dataParentsChildrenList_ofLabel [BEq β] (lab : β) : DAG α β → Option (α × (List β) × (List β))
| [] => .none
| x :: l => if x.label == lab then .some (x.data, x.parents, x.children) else (DAG.dataParentsChildrenList_ofLabel lab l)

def sDAG.dataParentsChildrenArray_ofLabel {α β : Type _} [Inhabited α] [Inhabited β] {store : Type _ → Type _} [ToIdx β store]
  [Repr (store β)] [Inhabited (store β)] [BEq (store β)] (lab : β) (d : sDAG α β store) : Option (α × (Array Nat) × (Array Nat)) :=
  match ToIdx.toIdx d.label_to_idx lab with
  | .some idx => let node := (d.dag.get! idx) ; .some (node.data, node.parents, node.children)
  | _ => .none


def sDAG.dataLabeledParentsChildrenArray_ofLabel {α β : Type _} [Inhabited α] [Inhabited β] {store : Type _ → Type _} [ToIdx β store]
  [Repr (store β)] [Inhabited (store β)] [BEq (store β)] (lab : β) (d : sDAG α β store) : Option (α × (Array β) × (Array β)) :=
  match sDAG.dataParentsChildrenArray_ofLabel lab d with
  | .some (data, pars, chils) =>
      (data, Array.mapF pars (fun i => d.idx_to_label.get! i), Array.mapF chils (fun i => d.idx_to_label.get! i))
  | _ => .none
