
import LeanGrow.F.Prototypes.MarkFour.Search

open Lean


inductive ActType where
| ofFor (n : Name) | ofBack (n : Name)  | ofForRW (n : Name)  | ofBackRW (n : Name)  | ofOther
deriving Inhabited, Repr, BEq

inductive mctsTree where
| root (state : SearchState) (kids : List mctsTree)
| leaf (act : ActType) (score apps : Nat) (state : SearchState)
| node (act : ActType) (score apps : Nat) (state : SearchState) (kids : List mctsTree)


def mctsTree.getState : mctsTree → SearchState
| .root s _ => s
| .leaf _ _ _ s => s
| .node _ _ _ s _ => s
