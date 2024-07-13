

import Lean

open Lean

structure DAGnode (α β : Type _) where
  name : β
  data : α
  parents : List β
deriving Repr, Inhabited, BEq

def DAG (α β : Type _) := List (DAGnode α β )

instance (α β : Type _) [Repr α] [Repr β]: Repr (DAG α β) where
  reprPrec := fun d i => List.repr d i

instance (α β : Type _) : Inhabited (DAG α β) where
  default := []

instance (α β : Type _) [BEq α] [BEq β]: BEq (DAG α β) where
  beq := fun l r => List.instBEq.beq l r

structure SizedDAG (α β : Type _) where
  size : Nat
  dag : DAG α β
deriving Repr, Inhabited, BEq

def SizedDAG.nameDataList (d : SizedDAG α β) : List (β × α) :=
  d.dag.map (fun ⟨n, D, _⟩ => (n,D) )

def DAG.nameDataList (d : DAG α β) : List (β × α) :=
  d.map (fun ⟨n, D, _⟩ => (n,D) )

def SizedDAG.DataParentsList [BEq β] (d : SizedDAG α β) (name : β) : Option (α × (List β)) :=
  let rec findName : DAG α β → Option (α × (List β))
    | [] => .none
    | x :: l => if x.name == name then .some (x.data, x.parents) else (findName l)
  findName d.dag

def DAG.DataParentsList [BEq β] (d : DAG α β) (name : β) : Option (α × (List β)) :=
  let rec findName : DAG α β → Option (α × (List β))
    | [] => .none
    | x :: l => if x.name == name then .some (x.data, x.parents) else (findName l)
  findName d

def DAG.ParentsList [BEq β] (name : β) : DAG α β → Option ((List β))
| [] => .none
| x :: l => if x.name == name then .some (x.parents) else (DAG.ParentsList name l)

def DAG.dataName [BEq β] (name : β) : DAG α β → Option (α)
| [] => .none
| x :: l => if x.name == name then .some (x.data) else (DAG.dataName name l)


-- haven't really tested this
partial def DAG.topo_sort (d : SizedDAG α Nat) (discard : RBTree Nat (instOrdNat.compare)) (count : Nat) : (List (DAGnode α Nat)) :=
  dbg_trace s!"On count {count}, discarded {discard.toList}"
  let rec find_sources (d : List (DAGnode α Nat)) (discard : RBTree Nat (instOrdNat.compare)) : (List (DAGnode α Nat)) × (RBTree Nat (instOrdNat.compare)) :=
    match d with
    | [] => ([], discard)
    | n :: rest => if n.parents.filter (fun x => !(discard.contains x)) = []
                   then let (da, di) := find_sources rest (discard.insert n.name) ; (n :: da, di)
                   else find_sources rest discard
  if count ≥ d.size
  then []
  else let (pass_da, pass_di) := find_sources d.dag discard
       ((DAG.topo_sort d pass_di (count + pass_da.length)) ++  pass_da.reverse)



-- dags are already topologically sorted (but in wrong order), also in the lctx
def SizeDAG.sinks_fst (d : SizedDAG α β) : SizedDAG α β :=
 {d with dag := List.reverse d.dag}

def DAG.find_sinks [Inhabited α] (D : SizedDAG α Nat) : (List (DAGnode α Nat)) :=
  let rec go (d : List (DAGnode α Nat)) (ref : Array (DAGnode α Nat) ) (candidates : RBTree Nat (instOrdNat.compare)) : List (DAGnode α Nat) :=
    match d with
    | [] => ((candidates.val.map (fun k _ => ref.get! k)).toArray.map (Sigma.snd)).toList
            -- massive hoop jumping. either get as array, or write API for RBMap.map
    | n :: rest =>
        let del_p := n.parents.foldl (fun (r) k => RBTree.erase r k) candidates
        go rest ref (RBTree.insert del_p n.name)
  go D.dag D.dag.toArray {}


def DAG.toString (e : α → String) : DAG α Nat → String
| [] => "[]"
| ⟨n, d, p⟩ :: rest => s!"⟨{n},{e d},{p}⟩ :: " ++ (DAG.toString e rest)


def SizedDAG.toString (e : α → String) : SizedDAG α Nat → String :=
 fun ⟨s, d⟩ => s!"⟨{s},{DAG.toString e d}⟩"
