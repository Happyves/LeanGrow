

import LeanGrow.Src.Core.Embedding.TestTools_fullRW


open Lean Meta

#check 1


unsafe def test_1 := testBackRw #[`Init.Data.List.Perm, `Init.Data.List.Range]



-- With context g(n : Nat) g(l : List Nat) and objects (n ∈ (l ++ (List.range (n.succ)))) run test_1

-- With context g(n : Nat) g(l : List Nat) and objects (n ∈ (l ++ (List.range (n+1)))) run test_1

/- In ↑, we see the shortcomming of PaIn-queries that consists in not finding
defeq patterns when syntactically equal ones have been found : since there are
theorems about List.range (n+1), those for List.rang n.succ are ignored ...

-/


#check List.Perm.mem_iff
#check List.range_succ
#check List.range_eq_range'

#check List.range_add
#check List.range_succ_eq_map

-- With context g(n : Nat) t(37 : 42 : m : List Nat) and objects (List.range n = m) run test_1

#check List.range_eq_nil
#check List.singleton_perm_singleton

-- With context g(n : Nat) g(l : List Nat) and objects ((List.range 42)[37]? = .some (List.count ((List.range n).length) l)) run test_1

#check List.Perm.count_eq
#check List.getElem?_range
#check List.length_range
#check List.length_zipIdx
#check List.Perm.length_eq

-- With context g(n : Nat) g(j : Nat) t(37 : 42 : m : Nat) g(h : j < n+1) and objects (((List.range n) ++ [m])[j]'(by simp ; exact h) = 42) run test_1

-- With context g(n : Nat) g(j : Nat) t(37 : 42 : m : Nat) t(37 : 67 : h : j < n+1) and objects (((List.range n) ++ [m])[j]'(by simp ; exact h) = 42) run test_1

-- With context g(n : Nat) t(42 : 42 : j : Nat) t(37 : 42 : m : Nat) t(37 : 67 : h : j < n+1) and objects (((List.range n) ++ [m])[j]'(by simp ; exact h) = 42) run test_1

#check List.range_one
