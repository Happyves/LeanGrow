

import Lean.Data.RBMap


-- # preDAG

structure pDAGnode (α β : Type _) where
  label : β
  data : α
  parents : List β
deriving Repr, Inhabited, BEq

def pDAG (α β : Type _) := List (pDAGnode α β )

instance (α β : Type _) [Repr α] [Repr β]: Repr (pDAG α β) where
  reprPrec := fun d i => List.repr d i

instance (α β : Type _) : Inhabited (pDAG α β) where
  default := []

instance (α β : Type _) [BEq α] [BEq β]: BEq (pDAG α β) where
  beq := fun l r => List.instBEq.beq l r

/-- Assumes distict labels-/
def pDAGnode.lbeq [BEq β] (a b : pDAGnode α β) : Bool :=
 BEq.beq a.label b.label



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

/-- Assumes distict labels-/
def DAGnode.lbeq [BEq β] (a b : DAGnode α β) : Bool :=
 BEq.beq a.label b.label



-- # sDAG

structure sDAGnode (α β : Type _) where
  real_label : β
  cache_label : Nat
  data : α
  parents : Array Nat
  children : Array Nat
deriving Repr, Inhabited, BEq

/-- Assumes distict labels-/
def sDAGnode.lbeq (a b : sDAGnode α β) : Bool :=
 BEq.beq a.cache_label b.cache_label


class ToIdx (β : Type _) (store : Type _ → Type _) where
  toIdx : (dataStruc : store β) → (label : β) → Option Nat
  extend : (dataStruc : store β) → (label : β) → (idx : Nat) → store β
  empty : store β


/-- `store` should be a data structure that will associate `β` to `Nat`,
for example `fun x => List (x × Nat)` or if `β` is `Nat`, `RBNode` or just `Nat → Nat`-/
structure sDAG (α β : Type _) (store : Type _ → Type _) [ToIdx β store]
  [Repr (store β)] [Inhabited (store β)] [BEq (store β)] where
  size : Nat
  dag : Array (sDAGnode α β)
  idx_to_label : Array β
  label_to_idx : store β
deriving Repr, Inhabited, BEq


instance ListToIdx (β : Type _) [BEq β] : ToIdx β (fun x => List (x × Nat)) where
  toIdx := fun D l => Prod.snd <$> (List.find? (fun x => (Prod.fst x) == l) D)
  extend := fun D l i => (l,i) :: D
  empty := []

open Lean in
instance RBNodeToIdx : ToIdx Nat (fun _ => RBNode Nat (fun _ => Nat)) where
  toIdx := fun D l => RBNode.find instOrdNat.compare D l
  extend := fun D l i => RBNode.insert instOrdNat.compare D l i
  empty := {}

instance IdToIdx : ToIdx Nat (fun _ => Nat → Nat) where
  toIdx := fun D l => D l
  extend := fun D _ _ => D
  empty := id
