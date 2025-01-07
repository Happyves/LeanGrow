

import LeanGrow.F.Ranking.WithStats.Types

def HypGoalThmState.query (scores : HypGoalThmState) (hyps goals : CExprTrie) : List (ActionType) :=
  let fst := SetTrieC.query hyps scores
  let snd := fst.map (fun st => SetTrieC.query goals st)
  snd.join

def HypGoalThmState.queryH (scores : HypGoalThmState) (hyps goals : CExprTrie) : List (ActionType) :=
  let fst := SetTrieC.queryHeaviests hyps scores
  let snd := fst.map (fun st => SetTrieC.query goals st) -- not for goals ???
  snd.join


def HypGoalThmState.make (samples : List (CExprTrie × List (CExprTrie × ActionType))) : HypGoalThmState :=
  SetTrieC.makeWVals (samples.map  (fun (t, subsam) => (t, SetTrieC.makeWVals subsam)))

/-
To investigate : add samples online to HypGoalThmState
-/

def HypGoalThmState.updateAll (scores : HypGoalThmState) (hyps goals : CExprTrie)
  (up : ActionType → ActionType) : HypGoalThmState :=
    SetTrieC.map hyps scores (fun x => SetTrieC.map goals x up)

def HypGoalThmState.updateDeepest (scores : HypGoalThmState) (hyps goals : CExprTrie)
  (up : ActionType → ActionType) : HypGoalThmState :=
    SetTrieC.mapDeepest hyps scores (fun x => SetTrieC.map goals x up) -- again, not for goals ?!?


def ActionType.upFor (thm : ByteArray) (up : Option Nat → Option Nat) (A : ActionType) : ActionType:=
  {A with ofFor := A.ofFor.upsert thm up}

def ActionType.upBack (thm : ByteArray) (up : Option Nat → Option Nat) (A : ActionType) : ActionType:=
  {A with ofBack := A.ofBack.upsert thm up}

def ActionType.upForRW (thm : ByteArray) (up : Option Nat → Option Nat) (A : ActionType) : ActionType:=
  {A with ofForRW := A.ofForRW.upsert thm up}

def ActionType.upBackRW (thm : ByteArray) (up : Option Nat → Option Nat) (A : ActionType) : ActionType:=
  {A with ofBackRW := A.ofBackRW.upsert thm up}
