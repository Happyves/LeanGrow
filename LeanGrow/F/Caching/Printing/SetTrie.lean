
import LeanGrow.F.Caching.Linking.SetTrie
import LeanGrow.F.Caching.Printing.API


open Lean


partial def sSetTrie.print (print_a : α → String) (print_b : β → String) (names_setTries : Nat → String) (names_keys : Nat → String) : sSetTrie α β → String
  | .leaf x => s!"SetTrie.leaf ({print_a x})"
  | .root c => s!"SetTrie.root {printList c (sSetTrie.print print_a print_b names_setTries names_keys)}"
  | .node b c => s!"SetTrie.node ({print_b b}) {printList c (sSetTrie.print print_a print_b names_setTries names_keys)}"
  | .snode b c => s!"SetTrie.node {names_keys b} {printList c (sSetTrie.print print_a print_b names_setTries names_keys)}"
  | .pointer n => names_setTries n
