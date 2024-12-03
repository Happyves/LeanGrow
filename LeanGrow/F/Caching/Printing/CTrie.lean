
import LeanGrow.F.Caching.Linking.CTrie

open Lean

partial def sCTrie.print (print : α → String) (names : Nat → String) : sCTrie α → String
  | .leaf .none => "CTrie.leaf Option.none"
  | .leaf (.some x) => s!"CTrie.leaf (Option.some ({print x}))"
  | .node1 .none a c => s!"CTrie.node1 Option.none {repr a} ({sCTrie.print print names c})"
  | .node1 (.some x) a c => s!"CTrie.node1 (Option.some ({print x})) {repr a} ({sCTrie.print print names c})"
  | .node .none a c => s!"CTrie.node Option.none {repr a} ({repr (c.map (sCTrie.print print names))})"
  | .node (.some x) a c => s!"CTrie.node (Option.some ({print x})) {repr a} ({repr (c.map (sCTrie.print print names))})"
  | .pointer n => names n
