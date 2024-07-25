

inductive QT (α β γ : Type _) where
| nil
| leaf (kx : α) (kb : β) (val :  γ)
| node (kx : α) (kb : β) (val : γ) (nw ne sw se : QT α β γ)
deriving Inhabited, BEq, Repr


def QT.find? [Ord α] [Ord β] (t : QT α β γ) (kx : α) (ky : β) : Option γ :=
  match t with
  | .nil => .none
  | .leaf x y v => if (compare x kx = .eq) ∧ (compare y ky = .eq) then .some v else .none
  | .node x y v nw ne sw se =>
        match compare x kx, compare y ky with
        | .eq, .eq => .some v
        | .eq, .lt => QT.find? se kx ky
        | .eq, .gt => QT.find? ne kx ky
        | .lt,  cy => if cy = .lt then QT.find? sw kx ky else QT.find? nw kx ky
        | .gt, cy => if cy = .lt then QT.find? se kx ky else QT.find? ne kx ky

def QT.update [Ord α] [Ord β] (t : QT α β γ) (kx : α) (ky : β) (f : γ → γ) : QT α β γ :=
  match t with
  |  .nil => .nil
  | .leaf x y v => if (compare x kx = .eq) ∧ (compare y ky = .eq) then .leaf x y (f v) else .leaf x y v
  | .node x y v nw ne sw se =>
        match compare x kx, compare y ky with
        | .eq, .eq => .node x y (f v) nw ne sw se
        | .eq, .lt => .node x y v nw ne sw (QT.update se kx ky f)
        | .eq, .gt => .node x y v nw (QT.update ne kx ky f) sw se
        | .lt,  cy => if cy = .lt then .node x y v nw ne (QT.update sw kx ky f) se else .node x y v (QT.update nw kx ky f) ne sw se
        | .gt, cy => if cy = .lt then .node x y v nw ne sw (QT.update se kx ky f) else .node x y v nw (QT.update ne kx ky f) sw se

def QT.insert [Ord α] [Ord β] (t : QT α β γ) (kx : α) (ky : β) (V : γ) : QT α β γ :=
  match t with
  | .nil => .leaf kx ky V
  | .leaf x y v =>
        match compare x kx, compare y ky with
        | .eq, .eq => .leaf x y v
        | .eq, .lt => .node x y v .nil .nil .nil (.leaf kx ky V)
        | .eq, .gt => .node x y v .nil (.leaf kx ky V) .nil .nil
        | .lt,  cy => if cy = .lt then .node x y v .nil .nil (.leaf kx ky V) .nil else .node x y v (.leaf kx ky V) .nil .nil .nil
        | .gt, cy => if cy = .lt then .node x y v .nil .nil .nil (.leaf kx ky V) else .node x y v .nil (.leaf kx ky V) .nil .nil
  | .node x y v nw ne sw se =>
        match compare x kx, compare y ky with
        | .eq, .eq => .node x y v nw ne sw se
        | .eq, .lt => .node x y v nw ne sw (QT.insert se kx ky V)
        | .eq, .gt => .node x y v nw (QT.insert ne kx ky V) sw se
        | .lt,  cy => if cy = .lt then .node x y v nw ne (QT.insert sw kx ky V) se else .node x y v (QT.insert nw kx ky V) ne sw se
        | .gt, cy => if cy = .lt then .node x y v nw ne sw (QT.insert se kx ky V) else .node x y v nw (QT.insert ne kx ky V) sw se

def QT.toString (as : α → String) (bs : β → String) (cs : γ → String) : QT α β γ → String
| .nil => "QT.nil"
| .leaf x y k => s!"QT.leaf ({as x}) ({bs y}) ({cs k})"
| .node x y v nw ne sw se => s!"QT.node ({as x}) ({bs y}) ({cs v}) ({QT.toString  as bs cs nw}) ({QT.toString  as bs cs ne}) ({QT.toString  as bs cs sw}) ({QT.toString  as bs cs se})"


def QT.upsert [Ord α] [Ord β] (t : QT α β γ) (kx : α) (ky : β) (f : Option γ → γ) : QT α β γ :=
  match t with
  | .nil => .leaf kx ky (f .none)
  | .leaf x y v =>
        match compare x kx, compare y ky with
        | .eq, .eq => .leaf x y (f (.some v))
        | .eq, .lt => .node x y v .nil .nil .nil (.leaf kx ky (f .none))
        | .eq, .gt => .node x y v .nil (.leaf kx ky (f (.none))) .nil .nil
        | .lt,  cy => if cy = .lt then .node x y v .nil .nil (.leaf kx ky (f (.none))) .nil else .node x y v (.leaf kx ky (f (.none))) .nil .nil .nil
        | .gt, cy => if cy = .lt then .node x y v .nil .nil .nil (.leaf kx ky (f (.none))) else .node x y v .nil (.leaf kx ky (f (.none))) .nil .nil
  | .node x y v nw ne sw se =>
        match compare x kx, compare y ky with
        | .eq, .eq => .node x y (f (.some v)) nw ne sw se
        | .eq, .lt => .node x y v nw ne sw (QT.insert se kx ky (f (.none)))
        | .eq, .gt => .node x y v nw (QT.insert ne kx ky (f (.none))) sw se
        | .lt,  cy => if cy = .lt then .node x y v nw ne (QT.insert sw kx ky (f (.none))) se else .node x y v (QT.insert nw kx ky (f (.none))) ne sw se
        | .gt, cy => if cy = .lt then .node x y v nw ne sw (QT.insert se kx ky (f (.none))) else .node x y v nw (QT.insert ne kx ky (f (.none))) sw se
