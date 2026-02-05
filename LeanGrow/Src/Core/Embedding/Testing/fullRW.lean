

import LeanGrow.Src.Core.Embedding.TestTools_fullRW


open Lean Meta

#check 1


unsafe def test_1 := testBackRw #[`Init.Data.List.Perm, `Init.Data.List.Range]

#check List.Perm.mem_iff
#check List.Perm.eq_nil
#check List.Perm.count_eq
#check List.getElem?_range
#check List.length_range
#check List.range_succ


-- With context g(n : Nat) g(l : List Nat) and objects (n ∈ (l ++ (List.range (n.succ)))) run test_1
-- ↓ should also have ↑  ???
--With context g(n : Nat) g(l : List Nat) and objects (n ∈ (l ++ (List.range (n+1)))) run test_1
