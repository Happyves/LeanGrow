

import LeanGrow.Src.Core.Embedding.TestTools_fullStd


open Lean Meta

#check 1


unsafe def test_1 := testBack #[`Init.Data.List.Basic, `Init.Data.List.Lemmas]


-- With context g(as : List Int) g(bs : List Int) g(cs : List Int) and objects (as ++ bs ++ cs = as ++ (bs ++ cs)) run test_1

#check List.append_assoc

-- With context g(l : List Int) g(h : l ≠ []) t(37 : 67 : m : List Int) and objects (l.head h ∈ m) run test_1

#check List.head_mem
#check List.mem_of_elem_eq_true
#check List.mem_of_mem_head?
#check List.mem_of_getLast?
-- and many more ; great sucess

-- With context g(p : Int → Bool) g(l : List Int) t(2 : 3 : α : Type) t(0 : 1 : m : List α) and objects ((List.filter p l).length ≤ m.length) run test_1

#check List.length_filter_le


-- With context g(p : Int → Bool) g(l : List Int) t(0 : 1 : m : List Int) and objects ((List.filter p m).length ≤ l.length) run test_1

-- With context t(0 : 1 : m : Int → Bool) g(l : List Int) and objects ((List.filter m l).length ≤ l.length) run test_1

-- With context g(p : Int → Bool) g(l : List Int) t(2 : 3 : α : Type) t(0 : 1 : m : (Int → Bool) → List Int → List Int) and objects ((m p l).length ≤ l.length) run test_1
-- failure ; expected ? List.filter is a const with a lnode-universe, so tnode match prohibited ?

-- With context g(p : Int → Bool) g(l : List Int) t(2 : 3 : α : Type) t(0 : 1 : m : (Int → Bool) → List Int → List α) and objects ((m p l).length ≤ l.length) run test_1
-- failure

-- With context g(l : List Int) t(2 : 3 : α : Type) t(0 : 1 : m : List α) and objects (m.length ≤ l.length ) run test_1
-- fails to unify ; expected ? As would assign tnode lnodes ?


-- With context g(l : List Int) and objects ((l.filter (42 == ·)).length ≤ l.length) run test_1

#check List.length_filter_le


-- With context g(α : Type) g(i : BEq α) g(l : List α) and objects ((l.filter (fun x => x == x)).length ≤ l.length) run test_1

-- With context g(l : List Int) u(n : Nat : l.length) and objects ((l.filter (42 == ·)).length ≤ n) run test_1
-- yay ; unode unfolded

-- With context g(l : List Int) u(n : Nat : l.length) t(0 : 1 : m : List Int) and objects ((m.filter (42 == ·)).length ≤ n) run test_1


-- With context g(l : List Int) g(l' : List Int) and objects (l = l') run test_1
-- status 0, ie expected fail ; no matching thm in modules ??

#check List.unzip_cons
#check List.mem_partition

-- With context g(as : List Int) g(a : Int) and objects (List.elem a (a :: as) = true) run test_1

#check List.elem_cons_self

-- With context g(α : Type) g(I1 : BEq α) g(I2 : LawfulBEq α) g(as : List α) g(a : α) and objects (List.elem a (a :: as) = true) run test_1


unsafe def test_2 := testForw #[`Init.Data.List.Basic, `Init.Data.List.Lemmas]

unsafe def test_2_1 := test_2 (.leaf (.mk #[0,1]))

tracing_mode .std
tracing_flags [
    (`testForw, TracingFlags.all), (`embedForwInterMain, TracingFlags.all), -- wouldn't print go and findSplit otherwise ...
    (`embedPropaInter, TracingFlags.all), (`embedForwInterMain.findSplit , TracingFlags.all),
    (`embedForwInterPostProcess', TracingFlags.all),
    (`embedForwInterMain.go, TracingFlags.all)]

With context g(as : List Int) g(a : Int) and objects run test_2_1

#check List.elem_cons_self
