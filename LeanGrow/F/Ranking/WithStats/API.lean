

import LeanGrow.F.Ranking.WithStats.Types

def HypGoalThm_toAprs.query (scores : HypGoalThm_toAprs) (hyps goals : CExprTrie) : List (ActionType) :=
  let fst := SetTrieC.query hyps scores
  let snd := fst.map (fun st => SetTrieC.query goals st)
  snd.join

def HypGoalThm_toAprs.queryH (scores : HypGoalThm_toAprs) (hyps goals : CExprTrie) : List (ActionType) :=
  let fst := SetTrieC.queryHeaviests hyps scores
  let snd := fst.map (fun st => SetTrieC.queryHeaviests goals st)
  snd.join
