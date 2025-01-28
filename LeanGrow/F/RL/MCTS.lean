

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
