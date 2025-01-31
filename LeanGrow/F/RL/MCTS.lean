

import LeanGrow.F.RL.Types
--import LeanGrow.F.Ranking.WithStats.API
-- painfull import clash due to technical debt...

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
  | .root _  kids => go 0 1 0 T kids
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
    | .root _ k :: _ => go 0 k -- 0 so that rand in [0,Tsize] is 0 if only root
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
  let r ← IO.rand 0 T.size -- same with get apps ? getApps
  return (T.selectExplore_core r)


def mctsTree.expandExploit (st : SearchState) : List (ActType × SearchState) :=
  sorry
-- ↑ will be based on a variant of ↓, where we also take note of the action type
#check search_step
-- here, we'll want to select the highests scoring actions according to current weights


def mctsTree.expandExplore (st : SearchState) : List (ActType × SearchState) :=
  sorry
-- here, we'll want to take a random action among all available ones
-- so we should have as SetTrieC will all theorems in it to take from
-- and choose whether to try induction etc.

-- We should do the following combos for select × expand : (exploit,exploit), (explore,exploit)  and (exploit,explore)
-- (explore,explore) will be trash ?


def mctsTree.simulate (st : SearchState) : Nat :=
  sorry
-- will return the score of the states gained from expantion
-- will boil down to running a fixed number of `search_step` and ranking the final state



/-- Affects the order by potentially prepending a leaf.
Expects dirs in same order as outputted by selection -/
def mctsTree.propagateWith (T : mctsTree) (addAT : ActType) (addST : SearchState) (addScore : Nat) (dirs : List Nat) : mctsTree :=
  let rec go : mctsTree → List Nat → mctsTree
    | .root s k, [] => .root s ((.leaf addAT addScore 1 addST) :: k)
    | .root s k, x :: xs => .root s (k.modifyNth (go · xs) x)
    | .leaf a s p S, [] => .node a (s+addScore) (p.succ) S ([(.leaf addAT addScore 1 addST)])
    | .node a s p S k, [] => .node a (s+addScore) (p.succ) S ((.leaf addAT addScore 1 addST) :: k)
    | .node a s p S k, x :: xs => .node a (s+addScore) (p.succ) S (k.modifyNth (go · xs) x)
    | _, _ => .root default []
  go T dirs.reverse


-- TODO : incorporate info of mctsTree to HypGoalThmState
-- Idea to integrate : make use of all nodes of the mctsTree, where the scores and
-- appearances should determine how much impact the modification on HypGoalThmState should
-- be made

def getHGTSkeys (st : SearchState) : List ((CExprTrie Nat) × List CExpr) :=
  -- replace with newer version of CExprTrie.
  -- first output should be ltx, second output is list of goals
  -- as list, where distinctions between ltxs of IntroTree
  sorry


partial def mctsTree.getKidsActData (T : mctsTree) : List (ActType × Nat × Nat) :=
  let rec go (done : List (ActType × Nat × Nat)) : List mctsTree → List (ActType × Nat × Nat)
    | [] => done
    | .root _ _ :: _ => []
    | .leaf a sc ap _ :: ts => go ((a,sc,ap) :: done) ts
    | .node a sc ap _ _  :: ts => go ((a,sc,ap) :: done) ts
  go [] [T]

def the_update (depth -- the depth of the node in the mctsTree
  score apps : Nat) (totalDepth : Float) -- convert once
  (total_over_kids : Float) -- ∑ i ∈ getKidsActData, score i * apps i
  : Float :=
  ((totalDepth - depth.toFloat) / totalDepth)
  * ((score.toFloat * apps.toFloat) / total_over_kids)
