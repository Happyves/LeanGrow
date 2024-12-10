
import Lean
import LeanGrow.F.Utils.Expr.ConstNames
import LeanGrow.F.Utils.Trie.Sorted

open Lean

/-
- fold over (← getEnv).constants
- maintain CTrie Nat where vals are hight
- maintain stack of thms to consider, starting with singlton the thm considered
- consider stack top : if in Trie, skip, else ↓ (can occur if appeared in proof of two separate thms used in main proof)
- get constants of proofs, filter those that are thms
- if names not in Trie, add them on stack, recurse
- else, get their hight, find max hight, set as current hight
- once stack empty, add entry to Trie which is maintained hight + 1 at key the initial thm

-/
