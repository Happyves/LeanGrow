

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
