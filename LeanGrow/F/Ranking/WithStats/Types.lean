
import LeanGrow.F.Utils.SetTrie.Specialized

open Lean

structure ActionType where
  ofFor : CTrie (Nat × Float)
  ofBack : CTrie (Nat × Float)
  ofForRW : CTrie (Nat × Float)
  ofBackRW : CTrie (Nat × Float)
  ofOther : Unit -- induction, noConfusion, quotient stuff ?
deriving Inhabited, Repr, BEq

def HypGoalThmState := SetTrieC (Nat × CExprTrie × (List (Nat × ActionType)))
