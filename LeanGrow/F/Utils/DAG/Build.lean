
import LeanGrow.F.Utils.DAG.Types
import LeanGrow.F.Utils.Array
import LeanGrow.F.Utils.List


open Lean


-- # pDAG and DAG

def pDAG.buildChildren [BEq β] (lab : β) : pDAG α β → List β
| [] => []
| ⟨l,_,p⟩ :: rest =>
    if p.contains lab then l :: (pDAG.buildChildren lab rest) else (pDAG.buildChildren lab rest)

def pDAG.toDAG [BEq β] (d : pDAG α β) : DAG α β :=
  let rec go (ref : pDAG α β) : pDAG α β → DAG α β
    | [] => []
    | ⟨label, data, parents ⟩ :: more =>
        let children := pDAG.buildChildren label ref
        ⟨label, data, parents, children⟩ :: (go ref more)
  go d d

def DAG.topDAG: DAG α β → pDAG α β
| [] => []
| ⟨label, data, parents, _⟩ :: more => ⟨label, data, parents ⟩ :: ( DAG.topDAG more)


-- # DAG and sDAG


def DAG.tosDAG {α β : Type _} [Inhabited α] [Inhabited β] [BEq α] [BEq β] {store : Type _ → Type _} [ToIdx β store]
  [Repr (store β)] [Inhabited (store β)] [BEq (store β)] (d : DAG α β) : Option (sDAG α β store) :=
  let size := List.length d
  let pre_dag := ((List.range size).map (List.get! d ·)).toArray
  let idx_to_label := Array.mapF pre_dag (fun x => x.label)
  let label_to_idx := ((List.range size).foldl (fun D i => ToIdx.extend D (idx_to_label.get! i) i ) (ToIdx.empty : store β))
  let node_snode : DAGnode α β → Nat → Option (sDAGnode α β) :=
      fun ⟨label, data, pars, chils⟩ idx =>
        let nps := pars.map (fun lab => ToIdx.toIdx label_to_idx lab)
        match (List.reduceOptionOrFail nps) with
        | .none => .none
        | .some rnps =>
            let ncs:= chils.map (fun lab => ToIdx.toIdx label_to_idx lab)
            match (List.reduceOptionOrFail ncs) with
            | .none => .none
            | .some rncs => .some ⟨label, idx, data, rnps.toArray, rncs.toArray⟩
  let dag? := pre_dag.mapFI node_snode
  if dag?.contains .none
  then .none
  else
    let dag := dag?.mapF (fun x => match x with | .some n => n | _ => default)
    .some ⟨size, dag, idx_to_label, label_to_idx⟩


def sDAG.toDAG {α β : Type _} [Inhabited α] [Inhabited β] {store : Type _ → Type _} [ToIdx β store]
  [Repr (store β)] [Inhabited (store β)] [BEq (store β)] (d : sDAG α β store) : DAG α β :=
  (List.range d.size).foldl
    (fun D sn_i =>
        let ⟨label, _, data, ps, cs⟩ := d.dag.get! sn_i
        let nps := ps.mapF (d.idx_to_label.get! · )
        let ncs := cs.mapF (d.idx_to_label.get! · )
        ⟨label, data, nps.toList, ncs.toList⟩ :: D
      )
    []

def DAG.tosDAGf {α β : Type _} [Inhabited α] [Inhabited β] [BEq β] {store : Type _ → Type _} [ToIdx β store]
  [Repr (store β)] [Inhabited (store β)] [BEq (store β)] (d : DAG α β) : Option (sDAG α β store) :=
  let size := List.length d
  let pre_dag := ((List.range size).map (List.get! d ·)).toArray
  let idx_to_label := Array.mapF pre_dag (fun x => x.label)
  let label_to_idx := ((List.range size).foldl (fun D i => ToIdx.extend D (idx_to_label.get! i) i ) (ToIdx.empty : store β))
  let node_snode : DAGnode α β → Nat → Option (sDAGnode α β) :=
      fun ⟨label, data, pars, chils⟩ idx =>
        let nps := pars.map (fun lab => ToIdx.toIdx label_to_idx lab)
        match (List.reduceOptionOrFail nps) with
        | .none => .none
        | .some rnps =>
            let ncs:= chils.map (fun lab => ToIdx.toIdx label_to_idx lab)
            match (List.reduceOptionOrFail ncs) with
            | .none => .none
            | .some rncs => .some ⟨label, idx, data, rnps.toArray, rncs.toArray⟩
  let dag? := pre_dag.mapFI node_snode
  if @Array.contains _ ⟨(@Option.instBEq _ ⟨sDAGnode.lbeq⟩).beq⟩ dag? .none
  then .none
  else
    let dag := dag?.mapF (fun x => match x with | .some n => n | _ => default)
    .some ⟨size, dag, idx_to_label, label_to_idx⟩
