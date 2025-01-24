

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

/-
To investigate : add samples online to HypGoalThmState
-/


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

def HypGoalThmState.updateDeepest (scores : HypGoalThmState) (hyps : CExprTrie) (goal : CExpr)
  (up : ActionType → ActionType) : HypGoalThmState :=
    SetTrieC.mapDeepest hyps scores (fun (xs,xt,xa) =>
      let td := xt.find? goal
      let mod := xa.foldl  (fun L (n,a) =>
        if td.contains n then (n, up a) :: L else (n, a) :: L
        ) []
      (xs,xt,mod))

def ActionType.upFor (thm : ByteArray) (up : Option Nat → Option Nat) (A : ActionType) : ActionType:=
  {A with ofFor := A.ofFor.upsert thm up}

def ActionType.upBack (thm : ByteArray) (up : Option Nat → Option Nat) (A : ActionType) : ActionType:=
  {A with ofBack := A.ofBack.upsert thm up}

def ActionType.upForRW (thm : ByteArray) (up : Option Nat → Option Nat) (A : ActionType) : ActionType:=
  {A with ofForRW := A.ofForRW.upsert thm up}

def ActionType.upBackRW (thm : ByteArray) (up : Option Nat → Option Nat) (A : ActionType) : ActionType:=
  {A with ofBackRW := A.ofBackRW.upsert thm up}
