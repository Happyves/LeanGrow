

import LeanGrow.F.Ranking.WithStats.Types

def HypGoalThmState.query (scores : HypGoalThmState) (hyps : CExprTrie) (goal : CExpr) : List (ActionType) :=
  let fst := SetTrieC.query hyps scores
  let snd := fst.map (fun (_,T,As) =>
      let ind := (T.find? goal).head!
      match As.find? (fun x => x.1 == ind) with
      | .some (_, a) => [a]
      | .none => []
      )
  snd.join

def HypGoalThmState.queryH (scores : HypGoalThmState) (hyps : CExprTrie) (goal : CExpr) : List (ActionType) :=
  let fst := SetTrieC.queryHeaviests hyps scores
  let snd := fst.map (fun (_,T,As) =>
      let ind := (T.find? goal).head!
      match As.find? (fun x => x.1 == ind) with
      | .some (_, a) => [a]
      | .none => []
      )
  snd.join


private def enumSplit (l : List (α × β)) : Nat × List (Nat × α) × List (Nat × β) :=
  let rec go (c : Nat) (doneA : List (Nat × α)) (doneB : List (Nat × β)) : List (α × β) → Nat × List (Nat × α) × List (Nat × β)
    | [] => (c,doneA,doneB)
    | (xa,xb) :: xs => go (c+1) ((c,xa) :: doneA) ((c,xb) :: doneB) xs
  go 0 [] [] l

def HypGoalThmState.make (samples : List (CExprTrie × List (CExpr × ActionType))) : HypGoalThmState :=
  SetTrieC.makeWVals (samples.map  (fun (t, subsam) =>
      let (sz,toT,Acts) := enumSplit subsam
      (t,(sz,CExprTrie.ofList toT, Acts))
      ))




def HypGoalThmState.insert (scores : HypGoalThmState) (hyps : CExprTrie) (goal : CExpr)
  (new : ActionType) : HypGoalThmState :=
    SetTrieC.map hyps scores (fun (xs,xt,xa) =>
      let nt := xt.insert goal xs
      let na := (xs,new) :: xa
      (xs+1,nt,na))

def HypGoalThmState.updateAll (scores : HypGoalThmState) (hyps : CExprTrie) (goal : CExpr)
  (up : ActionType → ActionType) : HypGoalThmState :=
    SetTrieC.map hyps scores (fun (xs,xt,xa) =>
      let td := xt.find? goal
      let mod := xa.foldl  (fun L (n,a) =>
        if td.contains n then (n, up a) :: L else (n, a) :: L
        ) []
      (xs,xt,mod))

/-
Investigate potential bug and confusion:
We want an update that takes a current HypGoalThmState, and a pair of
(hyps : CExprTrie) (goal : CExpr), and updates all entries of HypGoalThmState
that are *contained* in hyps (and in goal, if we choose to replace it with
a CExprTrie).
There may be a bug in SetTrieC.map, in the order expected by CExprTrie.contains
and the one expected in SetTrie.map ...
-/

def HypGoalThmState.updateDeepest (scores : HypGoalThmState) (hyps : CExprTrie) (goal : CExpr)
  (up : ActionType → ActionType) : HypGoalThmState :=
    SetTrieC.mapDeepest hyps scores (fun (xs,xt,xa) =>
      let td := xt.find? goal
      let mod := xa.foldl  (fun L (n,a) =>
        if td.contains n then (n, up a) :: L else (n, a) :: L
        ) []
      (xs,xt,mod))

def ActionType.upFor (thm : ByteArray) (up : Option (Nat × Float) → Option (Nat × Float)) (A : ActionType) : ActionType:=
  {A with ofFor := A.ofFor.upsert thm up}

def ActionType.upBack (thm : ByteArray) (up : Option (Nat × Float) → Option (Nat × Float)) (A : ActionType) : ActionType:=
  {A with ofBack := A.ofBack.upsert thm up}

def ActionType.upForRW (thm : ByteArray) (up : Option (Nat × Float) → Option (Nat × Float)) (A : ActionType) : ActionType:=
  {A with ofForRW := A.ofForRW.upsert thm up}

def ActionType.upBackRW (thm : ByteArray) (up : Option (Nat × Float) → Option (Nat × Float)) (A : ActionType) : ActionType:=
  {A with ofBackRW := A.ofBackRW.upsert thm up}


-- TODO: add purging operation, where we delete thms from the ActionType
-- entries that have too low scores ; this way, durring proof search,
-- we can simply try all entries of the ActionType, and we don't have to
-- do the ranking at that stage
-- (call it HypGoalThmState.RulesOfNature)
-- This is why we have entries (Nat × Float) for (appearances, score).
-- After a long traning sessions, we consider averaged scores, and keep
-- only the best ; we can then make a structure similar to HypGoalThmState
-- but where entries correspond to small lists of embedding data, corresponding
-- to the best scoring thms.
-- Problem is that scoring information will be lost if we train on new data
-- So maybe still store the HypGoalThmState for future training, but don't
-- use it for search.
