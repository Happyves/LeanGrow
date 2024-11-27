

import LeanGrow.F.Utils.ExprTrieRWez.Build

open Lean


/-
Goal is to get `(empty : γ) (merge : β → γ → γ) (max : γ → Option (δ × Nat))`
from `SetTrie.split_greedy_exact_hitting_set`, for example.

- Make map operation on the indices, wrap first indices in (0, ·)
- Merge by concatenating indicies, tagging the new ones with a new index
- Build, and number of occrunces should just be length of index lists
-/
