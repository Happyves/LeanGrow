

-- # preDAG

structure preDAGnode (α β : Type _) where
  label : β
  data : α
  parents : List β
deriving Repr, Inhabited, BEq

def preDAG (α β : Type _) := List (preDAGnode α β )

instance (α β : Type _) [Repr α] [Repr β]: Repr (preDAG α β) where
  reprPrec := fun d i => List.repr d i

instance (α β : Type _) : Inhabited (preDAG α β) where
  default := []

instance (α β : Type _) [BEq α] [BEq β]: BEq (preDAG α β) where
  beq := fun l r => List.instBEq.beq l r



-- # DAG

structure DAGnode (α β : Type _) where
  label : β
  data : α
  parents : List β
  children : List β
deriving Repr, Inhabited, BEq

def DAG (α β : Type _) := List (DAGnode α β )

instance (α β : Type _) [Repr α] [Repr β]: Repr (DAG α β) where
  reprPrec := fun d i => List.repr d i

instance (α β : Type _) : Inhabited (DAG α β) where
  default := []

instance (α β : Type _) [BEq α] [BEq β]: BEq (DAG α β) where
  beq := fun l r => List.instBEq.beq l r




-- # sDAG

structure sDAGnode (α β : Type _) where
  real_label : β
  cache_label : Nat
  data : α
  parents : Array Nat
  children : Array Nat
deriving Repr, Inhabited, BEq

/-- `store` should be a data structure that will associate `β` to `Nat`,
for example `fun x => List (x × Nat)` or if `β` is `Nat`, `RBNode` or just `Nat → Nat`-/
structure sDAG (α β : Type _) (store : Type _ → Type _)
  [Repr (store β)] [Inhabited (store β)] [BEq (store β)] where
  size : Nat
  dag : Array (sDAGnode α β)
  idx_to_label : Array β
  label_to_idx : store β
deriving Repr, Inhabited, BEq




#exit

-- Work on cachung and the stratification API before working on ↓

def DAG.toString (e : α → String) : DAG α Nat → String
| [] => "[]"
| ⟨n, d, p⟩ :: rest => s!"⟨{n},{e d},{p}⟩ :: " ++ (DAG.toString e rest)


def SizedDAG.toString (e : α → String) : SizedDAG α Nat → String :=
 fun ⟨s, d⟩ => s!"⟨{s},{DAG.toString e d}⟩"
