
import LeanGrow.F.Utils.SetTrie.Specialized

open Lean

structure ActionType where
  ofFor : CTrie Nat
  ofBack : CTrie Nat
  ofForRW : CTrie Nat
  ofBackRW : CTrie Nat
  ofOther : Unit -- induction, noConfusion, quotient stuff ?
deriving Inhabited, Repr, BEq

def HypGoalThmState := SetTrieC (Nat × CExprTrie × (List (Nat × ActionType)))
