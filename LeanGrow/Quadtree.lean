

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
        | .eq, .lt => QT.find? nw kx ky
        | .eq, .gt => QT.find? se kx ky
        | .lt,  cy => if cy = .lt then QT.find? ne kx ky else QT.find? se kx ky
        | .gt, cy => if cy = .lt then QT.find? nw kx ky else QT.find? sw kx ky

def QT.update [Ord α] [Ord β] (t : QT α β γ) (kx : α) (ky : β) (f : γ → γ) : QT α β γ :=
  match t with
  |  .nil => .nil
  | .leaf x y v => if (compare x kx = .eq) ∧ (compare y ky = .eq) then .leaf x y (f v) else .leaf x y v
  | .node x y v nw ne sw se =>
        --dbg_trace s!"{x} {kx} ; {y} {ky}"
        match compare x kx, compare y ky with
        | .eq, .eq => .node x y (f v) nw ne sw se
        | .eq, .lt => .node x y v (QT.update nw kx ky f) ne sw se
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
| .node x y v nw ne sw se => s!"QT.node ({as x}) ({bs y}) ({cs v}) ({QT.toString  as bs cs nw}) ({QT.toString  as bs cs ne}) ({QT.toString  as bs cs sw}) ({QT.toString  as bs cs se})"


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


inductive ValPost
| val (_ : Nat)
| postponed (_ : Nat × Nat × Nat × Nat)
deriving Inhabited, BEq, Repr

/-- Can contain nodes with 0 value, but who's decendent have values ; subtrees with only 0 vlaues are avoided however-/
partial def QT_process (lb lt hb ht : Nat) (comp : Nat → Nat → Nat) (d_count : Nat) : Option ((QT Nat Nat ValPost) × List (Nat × Nat × Nat × Nat)) :=
      let hh := (ht - hb) / 2
      let hl := (lt - lb) / 2
      if ht = hb
      then  if lt = lb
            then  let res := comp lb hb
                  if res = 0
                  then .none
                  else .some (.leaf lb hb (.val res), [])
            else .some (((List.range (lt - lb )).map (· + lb)).foldl (fun q x => let res := comp x hb ; if res = 0 then q else q.insert x hb (.val res)) QT.nil, [])
      else  if lt = lb
            then .some (((List.range (ht - hb)).map (· + hb)).foldl (fun q x => let res := comp lb x ; if res = 0 then q else q.insert lb x (.val res)) QT.nil, [])
            else  if d_count = 0
                  then  .some (.leaf (lb+ hl) (hb + hh) (.postponed (lb, lt, hb, ht)), [(lb, lt, hb, ht)])
                  else  match QT_process lb (lb + hl) (hb + hh + 1) ht comp (d_count - 1) with
                        | .some (NW, lNW) =>
                              match QT_process (lb + hl + 1) lt (hb + hh + 1) ht comp (d_count - 1) with
                              | .some (NE, lNE) =>
                                    match QT_process lb (lb + hl) hb (hb + hh) comp (d_count - 1) with
                                    | .some (SW, lSW) =>
                                          match QT_process (lb + hl + 1) lt hb (hb + hh) comp (d_count - 1) with
                                          | .some (SE, lSE) =>
                                                .some (.node (lb+ hl) (hb + hh) (.val (comp (lb+ hl) (hb + hh))) NW NE SW SE, lNW ++ lNE ++ lSW ++ lSE)
                                          | .none =>
                                                .some (.node (lb+ hl) (hb + hh) (.val (comp (lb+ hl) (hb + hh))) NW NE SW .nil, lNW ++ lNE ++ lSW)
                                    | .none =>
                                           match QT_process (lb + hl + 1) lt hb (hb + hh) comp (d_count - 1) with
                                          | .some (SE, lSE) =>
                                                .some (.node (lb+ hl) (hb + hh) (.val (comp (lb+ hl) (hb + hh))) NW NE .nil SE, lNW ++ lNE ++ lSE)
                                          | .none =>
                                                .some (.node (lb+ hl) (hb + hh) (.val (comp (lb+ hl) (hb + hh))) NW NE .nil .nil, lNW ++ lNE)
                              | .none =>
                                    match QT_process lb (lb + hl) hb (hb + hh) comp (d_count - 1) with
                                    | .some (SW, lSW) =>
                                          match QT_process (lb + hl + 1) lt hb (hb + hh) comp (d_count - 1) with
                                          | .some (SE, lSE) =>
                                                .some (.node (lb+ hl) (hb + hh) (.val (comp (lb+ hl) (hb + hh))) NW .nil SW SE, lNW ++ lSW ++ lSE)
                                          | .none =>
                                                .some (.node (lb+ hl) (hb + hh) (.val (comp (lb+ hl) (hb + hh))) NW .nil SW .nil, lNW ++ lSW)
                                    | .none =>
                                           match QT_process (lb + hl + 1) lt hb (hb + hh) comp (d_count - 1) with
                                          | .some (SE, lSE) =>
                                                .some (.node (lb+ hl) (hb + hh) (.val (comp (lb+ hl) (hb + hh))) NW .nil .nil SE, lNW ++ lSE)
                                          | .none =>
                                                .some (.node (lb+ hl) (hb + hh) (.val (comp (lb+ hl) (hb + hh))) NW .nil .nil .nil, lNW )
                        | .none =>
                              match QT_process (lb + hl + 1) lt (hb + hh + 1) ht comp (d_count - 1) with
                              | .some (NE, lNE) =>
                                    match QT_process lb (lb + hl) hb (hb + hh) comp (d_count - 1) with
                                    | .some (SW, lSW) =>
                                          match QT_process (lb + hl + 1) lt hb (hb + hh) comp (d_count - 1) with
                                          | .some (SE, lSE) =>
                                                .some (.node (lb+ hl) (hb + hh) (.val (comp (lb+ hl) (hb + hh))) .nil NE SW SE, lNE ++ lSW ++ lSE)
                                          | .none =>
                                                .some (.node (lb+ hl) (hb + hh) (.val (comp (lb+ hl) (hb + hh))) .nil NE SW .nil, lNE ++ lSW)
                                    | .none =>
                                           match QT_process (lb + hl + 1) lt hb (hb + hh) comp (d_count - 1) with
                                          | .some (SE, lSE) =>
                                                .some (.node (lb+ hl) (hb + hh) (.val (comp (lb+ hl) (hb + hh))) .nil NE .nil SE,  lNE ++ lSE)
                                          | .none =>
                                                .some (.node (lb+ hl) (hb + hh) (.val (comp (lb+ hl) (hb + hh))) .nil NE .nil .nil, lNE)
                              | .none =>
                                    match QT_process lb (lb + hl) hb (hb + hh) comp (d_count - 1) with
                                    | .some (SW, lSW) =>
                                          match QT_process (lb + hl + 1) lt hb (hb + hh) comp (d_count - 1) with
                                          | .some (SE, lSE) =>
                                                .some (.node (lb+ hl) (hb + hh) (.val (comp (lb+ hl) (hb + hh))) .nil .nil SW SE, lSW ++ lSE)
                                          | .none =>
                                                .some (.node (lb+ hl) (hb + hh) (.val (comp (lb+ hl) (hb + hh))) .nil .nil SW .nil, lSW)
                                    | .none =>
                                           match QT_process (lb + hl + 1) lt hb (hb + hh) comp (d_count - 1) with
                                          | .some (SE, lSE) =>
                                                .some (.node (lb+ hl) (hb + hh) (.val (comp (lb+ hl) (hb + hh))) .nil .nil .nil SE, lSE)
                                          | .none =>
                                                let res := comp (lb+ hl) (hb + hh)
                                                if res = 0
                                                then  .none
                                                else  .some (.leaf (lb+ hl) (hb + hh) (.val (res)), [])


partial def QT_build (lb lt hb ht : Nat) (comp : Nat → Nat → Nat) (depth : Nat) : List (String × (QT Nat Nat ValPost)) :=
      match QT_process lb lt hb ht comp depth with
      | .none => [(s!"qt_{lb}_{lt}_{hb}_{ht}", QT.nil)]
      | .some (qt, pointers) =>
            let go := (pointers.map (fun (x,y,z,w) => QT_build x y z w comp depth)).join
            go ++ [(s!"qt_{lb}_{lt}_{hb}_{ht}", qt)]

inductive Wrap
| val (_ : Nat)
| postponed (_ : QT Nat Nat Wrap)

def ValPost.toStringTrick : ValPost → String
| .val n => s!"Wrap.val {instToStringNat.toString n}"
| .postponed (lb, lt, hb, ht) => s!"Wrap.postponed qt_{lb}_{lt}_{hb}_{ht}"

#eval QT_build 0 10 0 10 (fun x y => if x^2 + y^2 ≥ 50 then 0 else x^2 + y^2) 3
#eval QT_build 0 10 0 10 (fun x y => if x^2 + y^2 ≥ 30 then 0 else x^2 + y^2) 3

#eval (( QT_build 0 10 0 10 (fun x y => if x^2 + y^2 ≥ 30 then 0 else x^2 + y^2) 3)).map (fun (n,t) => (n,(QT.toString instToStringNat.toString instToStringNat.toString ValPost.toStringTrick) t))

namespace TestingStuff

def qt_0_1_6_7 : QT Nat Nat Wrap := QT.nil

def qt_3_4_6_7 : QT Nat Nat Wrap := QT.nil

def qt_6_7_6_7 : QT Nat Nat Wrap := QT.nil

def qt_0_1_3_4 : QT Nat Nat Wrap := QT.node (0) (3) (Wrap.val 9) (QT.leaf (0) (4) (Wrap.val 16)) (QT.leaf (1) (4) (Wrap.val 17)) (QT.leaf (0) (3) (Wrap.val 9)) (QT.leaf (1) (3) (Wrap.val 10))

def qt_3_4_3_4  : QT Nat Nat Wrap := QT.node (3) (3) (Wrap.val 18) (QT.leaf (3) (4) (Wrap.val 25)) (QT.nil) (QT.leaf (3) (3) (Wrap.val 18)) (QT.leaf (4) (3) (Wrap.val 25))

def qt_0_1_0_1  : QT Nat Nat Wrap := QT.node (0) (0) (Wrap.val 0) (QT.leaf (0) (1) (Wrap.val 1)) (QT.leaf (1) (1) (Wrap.val 2)) (QT.nil) (QT.leaf (1) (0) (Wrap.val 1))

def qt_3_4_0_1  : QT Nat Nat Wrap := QT.node (3) (0) (Wrap.val 9) (QT.leaf (3) (1) (Wrap.val 10)) (QT.leaf (4) (1) (Wrap.val 17)) (QT.leaf (3) (0) (Wrap.val 9)) (QT.leaf (4) (0) (Wrap.val 16))

def qt_6_7_3_4  : QT Nat Nat Wrap := QT.nil

def qt_6_7_0_1  : QT Nat Nat Wrap := QT.nil

def qt_0_10_0_10  : QT Nat Nat Wrap := QT.node (5) (5) (Wrap.val 0) (QT.node (2) (8) (Wrap.val 0) (QT.node (1) (9) (Wrap.val 0) (QT.nil) (QT.nil) (QT.nil) (QT.nil)) (QT.node (4) (9) (Wrap.val 0) (QT.nil) (QT.nil) (QT.nil) (QT.nil)) (QT.node (1) (7) (Wrap.val 0) (QT.nil) (QT.nil) (QT.leaf (0) (6) (Wrap.postponed qt_0_1_6_7)) (QT.nil)) (QT.node (4) (7) (Wrap.val 0) (QT.nil) (QT.nil) (QT.leaf (3) (6) (Wrap.postponed qt_3_4_6_7)) (QT.nil))) (QT.node (8) (8) (Wrap.val 0) (QT.node (7) (9) (Wrap.val 0) (QT.nil) (QT.nil) (QT.nil) (QT.nil)) (QT.nil) (QT.node (7) (7) (Wrap.val 0) (QT.nil) (QT.nil) (QT.leaf (6) (6) (Wrap.postponed qt_6_7_6_7)) (QT.nil)) (QT.node (9) (7) (Wrap.val 0) (QT.nil) (QT.nil) (QT.nil) (QT.nil))) (QT.node (2) (2) (Wrap.val 8) (QT.node (1) (4) (Wrap.val 17) (QT.leaf (0) (5) (Wrap.val 25)) (QT.leaf (2) (5) (Wrap.val 29)) (QT.leaf (0) (3) (Wrap.postponed qt_0_1_3_4)) (QT.leaf (2) (3) (Wrap.val 13))) (QT.node (4) (4) (Wrap.val 0) (QT.nil) (QT.nil) (QT.leaf (3) (3) (Wrap.postponed qt_3_4_3_4)) (QT.nil)) (QT.node (1) (1) (Wrap.val 2) (QT.leaf (0) (2) (Wrap.val 4)) (QT.leaf (2) (2) (Wrap.val 8)) (QT.leaf (0) (0) (Wrap.postponed qt_0_1_0_1)) (QT.leaf (2) (0) (Wrap.val 4))) (QT.node (4) (1) (Wrap.val 17) (QT.leaf (3) (2) (Wrap.val 13)) (QT.leaf (5) (2) (Wrap.val 29)) (QT.leaf (3) (0) (Wrap.postponed qt_3_4_0_1)) (QT.leaf (5) (0) (Wrap.val 25)))) (QT.node (8) (2) (Wrap.val 0) (QT.node (7) (4) (Wrap.val 0) (QT.nil) (QT.nil) (QT.leaf (6) (3) (Wrap.postponed qt_6_7_3_4)) (QT.nil)) (QT.node (9) (4) (Wrap.val 0) (QT.nil) (QT.nil) (QT.nil) (QT.nil)) (QT.node (7) (1) (Wrap.val 0) (QT.nil) (QT.nil) (QT.leaf (6) (0) (Wrap.postponed qt_6_7_0_1)) (QT.nil)) (QT.node (9) (1) (Wrap.val 0) (QT.nil) (QT.nil) (QT.nil) (QT.nil)))

end TestingStuff


def QT.findP (t : QT Nat Nat Wrap) (kx ky : Nat) : Option Nat :=
  let rec unwrap (v : Wrap) :=
      match v with
      | .val w => .some w
      | .postponed qt => QT.findP qt kx ky
  match t with
  | .nil => .none
  | .leaf x y v =>
            match v with
            | .val w =>
                  if (compare x kx = .eq) ∧ (compare y ky = .eq)
                  then .some w
                  else  .none
            | .postponed qt => QT.findP qt kx ky
  | .node x y v nw ne sw se =>
        match compare x kx, compare y ky with
        | .eq, .eq => unwrap v
        | .eq, .lt => QT.findP nw kx ky
        | .eq, .gt => QT.findP se kx ky
        | .lt,  cy => if cy = .lt then QT.findP ne kx ky else QT.findP se kx ky
        | .gt, cy => if cy = .lt then QT.findP nw kx ky else QT.findP sw kx ky

#eval QT.findP TestingStuff.qt_0_10_0_10 0 3

#eval timeit "" (do return QT.findP TestingStuff.qt_0_10_0_10 3 4)

#eval timeit "" (do return QT.findP TestingStuff.qt_0_10_0_10 1 1)

#eval timeit "" (do return QT.findP TestingStuff.qt_0_10_0_10 4 1)
