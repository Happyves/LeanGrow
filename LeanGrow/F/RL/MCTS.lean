

import LeanGrow.F.RL.Types

open Lean


def mctsTree.getBestChild? (T : mctsTree) : Option (Nat × mctsTree) :=
  let rec go (mS mA c : Nat) (cand : mctsTree) : List mctsTree → (Nat × mctsTree)
    | [] => (c,cand)
    | nx :: more =>
        match nx with
        | .root _ _ => go 0 1 (c+1) nx more
        | .leaf _ sc aps _ =>  if sc*mA > mS*aps then go sc aps c nx more else go mS mA (c+1) cand more
        | .node _ sc aps _ _ => if sc*mA > mS*aps then go sc aps c nx more else go mS mA (c+1) cand more
  match T with
  | .node _ _ _ _ kids => go 0 1 0 T kids
  | _ => .none


partial def mctsTree.selectExploit (T : mctsTree) : SearchState × List Nat :=
  let rec go (dirs : List Nat) (t : mctsTree) : SearchState × List Nat :=
    match t.getBestChild? with
    | .some (idx,kid) => go (idx :: dirs) kid
    | .none => (t.getState, dirs)
  go [] T


#check IO.rand

/-
- if leaf, return
- get sum of children apps + 1
- get rand IO in that range
- if 0 stay at current root and return
- else, add aps from kids till above rand, and select that child
→ uniform proba on noes of tree

-/


partial def mctsTree.getApps (T : mctsTree) : Nat :=
  let rec go (c : Nat) : List mctsTree → Nat
    | [] => c
    | .root _ k :: _ => go c k
    | .leaf _ _ a _ :: ts => go (a+c) ts
    | .node _ _ a _ k  :: ts => go (a+c) (k ++ ts)
  go 0 [T]

partial def mctsTree.size (T : mctsTree) : Nat :=
  let rec go (c : Nat) : List mctsTree → Nat
    | [] => c
    | .root _ k :: _ => go 1 k
    | .leaf _ _ _ _ :: ts => go (c.succ) ts
    | .node _ _ _ _ k  :: ts => go (c.succ) (k ++ ts)
  go 0 [T]

partial def mctsTree.selectExplore_core (T : mctsTree) (rand : Nat): SearchState × List Nat :=
  let rec go (s : Nat) : List (mctsTree × List Nat) → SearchState × List Nat
    | [] => (default,[])
    | (.root st k, _) :: _ =>
          if rand = 0 then (st,[]) else go 1 (k.map (fun x => (x,[])))
    | (.leaf _ _ _ st, dirs) :: ts =>
          if rand = s then (st,dirs) else go (s+1) ts
    | (.node _ _ _ st k, dirs) :: ts =>
          if rand = s then (st,dirs) else go (s+1) ((k.enum.map (fun (p,t) => (t, p :: dirs)) ) ++ ts)
  go 0 [(T,[])]

#eval List.enum [3,3,3]


def mctsTree.selectExplore (T : mctsTree) : IO (SearchState × List Nat) := do
  let r ← IO.rand 0 T.size
  return (T.selectExplore_core r)
