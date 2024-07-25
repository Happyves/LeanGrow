

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
        | .gt, cy => if cy = .gt then QT.find? se kx ky else QT.find? ne kx ky

def QT.update [Ord α] [Ord β] [ToString α] [ToString β] (t : QT α β γ) (kx : α) (ky : β) (f : γ → γ) : QT α β γ :=
  match t with
  |  .nil => .nil
  | .leaf x y v => if (compare x kx = .eq) ∧ (compare y ky = .eq) then .leaf x y (f v) else .leaf x y v
  | .node x y v nw ne sw se =>
        dbg_trace s!"{x} {kx} ; {y} {ky}"
        match compare x kx, compare y ky with
        | .eq, .eq => .node x y (f v) nw ne sw se
        | .eq, .lt => .node x y v nw (QT.update ne kx ky f) sw se
        | .eq, .gt => .node x y v nw ne sw (QT.update se kx ky f)
        | .lt, cy => if cy = .lt then .node x y v nw (QT.update ne kx ky f) sw se else .node x y v nw ne sw (QT.update se kx ky f)
        | .gt, cy => if cy = .lt then .node x y v (QT.update nw kx ky f) ne sw se else .node x y v nw ne (QT.update sw kx ky f) se

#reduce compare 5 2


-- FIX ↓ according to ↑

def QT.insert [Ord α] [Ord β] (t : QT α β γ) (kx : α) (ky : β) (V : γ) : QT α β γ :=
  match t with
  | .nil => .leaf kx ky V
  | .leaf x y v =>
        match compare x kx, compare y ky with
        | .eq, .eq => .leaf x y v
        | .eq, .lt => .node x y v .nil .nil .nil (.leaf kx ky V)
        | .eq, .gt => .node x y v .nil (.leaf kx ky V) .nil .nil
        | .lt,  cy => if cy = .gt then .node x y v .nil .nil (.leaf kx ky V) .nil else .node x y v (.leaf kx ky V) .nil .nil .nil
        | .gt, cy => if cy = .lt then .node x y v .nil .nil .nil (.leaf kx ky V) else .node x y v .nil (.leaf kx ky V) .nil .nil
  | .node x y v nw ne sw se =>
        match compare x kx, compare y ky with
        | .eq, .eq => .node x y v nw ne sw se
        | .eq, .lt => .node x y v nw ne sw (QT.insert se kx ky V)
        | .eq, .gt => .node x y v nw (QT.insert ne kx ky V) sw se
        | .lt,  cy => if cy = .gt then .node x y v nw ne (QT.insert sw kx ky V) se else .node x y v (QT.insert nw kx ky V) ne sw se
        | .gt, cy => if cy = .lt then .node x y v nw ne sw (QT.insert se kx ky V) else .node x y v nw (QT.insert ne kx ky V) sw se

def QT.toString (as : α → String) (bs : β → String) (cs : γ → String) : QT α β γ → String
| .nil => "QT.nil"
| .leaf x y k => s!"QT.leaf ({as x}) ({bs y}) ({cs k})"
| .node x y v nw ne sw se => s!"QT.node ({as x}) ({bs y}) ({cs v}) \n({QT.toString  as bs cs nw}) \n({QT.toString  as bs cs ne}) \n({QT.toString  as bs cs sw}) \n({QT.toString  as bs cs se})"


def QT.upsert [Ord α] [Ord β] (t : QT α β γ) (kx : α) (ky : β) (f : Option γ → γ) : QT α β γ :=
  match t with
  | .nil => .leaf kx ky (f .none)
  | .leaf x y v =>
        match compare x kx, compare y ky with
        | .eq, .eq => .leaf x y (f (.some v))
        | .eq, .lt => .node x y v .nil .nil .nil (.leaf kx ky (f .none))
        | .eq, .gt => .node x y v .nil (.leaf kx ky (f (.none))) .nil .nil
        | .lt,  cy => if cy = .gt then .node x y v .nil .nil (.leaf kx ky (f (.none))) .nil else .node x y v (.leaf kx ky (f (.none))) .nil .nil .nil
        | .gt, cy => if cy = .lt then .node x y v .nil .nil .nil (.leaf kx ky (f (.none))) else .node x y v .nil (.leaf kx ky (f (.none))) .nil .nil
  | .node x y v nw ne sw se =>
        match compare x kx, compare y ky with
        | .eq, .eq => .node x y (f (.some v)) nw ne sw se
        | .eq, .lt => .node x y v nw ne sw (QT.upsert se kx ky f)
        | .eq, .gt => .node x y v nw (QT.upsert ne kx ky f) sw se
        | .lt,  cy => if cy = .gt then .node x y v nw ne (QT.upsert sw kx ky f) se else .node x y v (QT.upsert nw kx ky f) ne sw se
        | .gt, cy => if cy = .lt then .node x y v nw ne sw (QT.upsert se kx ky f) else .node x y v nw (QT.upsert ne kx ky f) sw se


partial def QT_initialize (lb lt hb ht : Nat) : QT Nat Nat Nat :=
      let hh := (ht - hb) / 2
      let hl := (lt - lb) / 2
      if ht = hb
      then  if lt = lb
            then .leaf lb hb 0
            else ((List.range (lt - lb )).map (· + lb)).foldl (fun q x => q.insert x hb 0) QT.nil
      else  if lt = lb
            then ((List.range (ht - hb)).map (· + hb)).foldl (fun q x => q.insert lb x 0) QT.nil
            else .node (lb+ hl) (hb + hh) 0 (QT_initialize lb (lb + hl) (hb + hh + 1) ht) (QT_initialize (lb + hl + 1) lt (hb + hh + 1) ht ) (QT_initialize lb (lb + hl) hb (hb + hh) ) (QT_initialize (lb + hl + 1) lt hb (hb + hh))


#eval QT_initialize 0 10 0 10
#eval QT_initialize 0 11 0 11

#eval (QT_initialize 0 10 0 10).update 1 9 Nat.succ

/-
Make version of QT_initialize where in phase where we make node, we run a computation,
indexed by the keys. In my context, that would be finding the clusters in the cluster arrays
index by these keys, and computing how many thms have their goal in the second cluster.

Also, wrap the values in Except and maintain some sort of depth counter, so that when depth reached,
we place a leaf with the name of the new QT to look at...
So maybe output should be list of pairs of a string (which will be the name of qt in source), and the corresponding qt
-/
