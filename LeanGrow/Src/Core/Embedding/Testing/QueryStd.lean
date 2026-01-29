

import LeanGrow.Src.Core.Embedding.TestTools_QueryStd


open Lean


#check Int.le_add_one
#check Int.le_add_of_nonneg_left
#check Int.le_add_of_nonneg_right

def testSet_1 := #[``Int.le_add_one, ``Int.le_add_of_nonneg_left, ``Int.le_add_of_nonneg_right]

def test_1_1 := testSandbox_embedForwIncludeCoreS testSet_1

-- tracing_mode .std
-- tracing_flags [(`PaInG.embedForwIncludeCore.go, TracingFlags.all)]

-- With context g(n : Int) g(m : Int) g(h1 : 0 ≤ n) g(h1 : 0 ≤ m) and objects run test_1_1

def test_1_2 := testSandbox_embedForwInterCoreS testSet_1

-- tracing_mode .std
-- tracing_flags [(`PaInG.embedForwInterCore.go, TracingFlags.all)]

-- With context g(n : Int) g(m : Int) g(h1 : 0 ≤ n) g(h1 : 0 ≤ m) and objects run test_1_2



def test_2 := testSandbox_embedBackMainS testSet_1


-- tracing_mode .std
-- tracing_flags [(`PaInG.embedBackCore, TracingFlags.all)]


-- With context g(n : Int) g(m : Int) and objects (n ≤ (n + m)) run test_2

-- With context g(n : Int) g(m : Int) and objects (n ≤ (m + n)) run test_2

-- With context g(n : Int) g(m : Int) and objects (n ≤ (m + 1)) run test_2

-- With context g(n : Int) g(m : Int) and objects (n ≤ (n + 1)) run test_2


unsafe def test_3_1 := testLoad_embedForwIncludeCoreS #[`Init.Data.List.Basic, `Init.Data.List.Lemmas]

-- tracing_mode .std
-- tracing_flags [(`PaInG.embedForwIncludeCore.go, TracingFlags.all)]

-- With context g(l : List Int) g(h : l.getLast? = .some 5)  and objects run test_3_1

-- Get interesting ones from ↑, ie. ↓, by ctrl+F `g.0`
#check List.mem_of_getLast?
#check List.Lex.rel
#check List.filterMap_cons_some
#check List.getLast_of_getLast?_eq_some
#check List.getLast!_of_getLast?
#check List.filterMap_replicate_of_some

-- With context g(l : List Int) u(a : Option Int : Option.some 5) g(h : l.getLast? = a) and objects run test_3_1
-- u not unfolded


/-- Remember that this is not a forward query, it is only a test.
We load that cache settries just to have something big to test on.
The return will not include all assignements requied by a forward step.
-/
unsafe def test_3_2 := testLoad_embedForwInterCoreS #[`Init.Data.List.Basic, `Init.Data.List.Lemmas]


-- tracing_mode .std
-- tracing_flags [(`PaInG.embedForwInterCore.go, TracingFlags.all)]


-- With context g(a : List Int) u(b : List Int : [1,2,3]) and objects run test_3_2

#check List.mem_append_right
#check List.mem_append_left
#check List.Mem.below.head
#check List.eq_replicate_or_eq_replicate_append_cons
#check List.length_filterMap_le
#check List.length_filter_le
#check List.eq_nil_or_concat
#check List.filter_sublist


-- With context g(l : List Int) g(h : l.getLast? = .some 5) and objects run test_3_2

#check List.mem_of_getLast?

-- With context g(l : List Int) u(a : Option Int : Option.some 5) g(h : l.getLast? = a) and objects run test_3_2
-- u not unfolded


-- With context g(l : List Int) g(l' : List Int) g(h : l ++ l' ≠ []) and objects run test_3_2


#check List.append_ne_nil_of_left_ne_nil
#check List.append_ne_nil_of_right_ne_nil
#check List.exists_mem_of_ne_nil
#check List.head_mem
#check List.getLast_mem
#check List.exists_cons_of_ne_nil
#check List.mem_of_ne_of_mem
#check List.getLast_mem_getLast?
#check List.head_mem_head?


unsafe def test_4 := testLoad_embedBackMainS #[`Init.Data.List.Basic, `Init.Data.List.Lemmas]


-- With context g(as : List Int) g(bs : List Int) g(cs : List Int) and objects (as ++ bs ++ cs = as ++ (bs ++ cs)) run test_4

#check List.append_assoc

-- With context g(l : List Int) g(h : l ≠ []) t(0 : 1 : m : List Int) and objects (l.head h ∈ m) run test_4

#check List.head_mem
#check List.mem_of_elem_eq_true
#check List.mem_of_mem_head?
#check List.mem_of_getLast?
-- and many more ; great sucess

-- With context g(p : Int → Bool) g(l : List Int) t(2 : 3 : α : Type) t(0 : 1 : m : List α) and objects ((List.filter p l).length ≤ m.length) run test_4

#check List.length_filter_le

tracing_mode .std
tracing_flags [(`PaInG.embedBackCore, TracingFlags.all),
               (`PaInG.embedBackDefEqCore.load, TracingFlags.all),
               (`PaInG.embedLnodes, TracingFlags.all)]

-- With context g(p : Int → Bool) g(l : List Int) t(0 : 1 : m : List Int) and objects ((List.filter p m).length ≤ l.length) run test_4

-- With context t(0 : 1 : m : Int → Bool) g(l : List Int) and objects ((List.filter m l).length ≤ l.length) run test_4

-- With context g(p : Int → Bool) g(l : List Int) t(2 : 3 : α : Type) t(0 : 1 : m : (Int → Bool) → List Int → List Int) and objects ((m p l).length ≤ l.length) run test_4
-- failure ; expected ? List.filter is a const with a lnode-universe, so tnode match prohibited ?

-- With context g(p : Int → Bool) g(l : List Int) t(2 : 3 : α : Type) t(0 : 1 : m : (Int → Bool) → List Int → List α) and objects ((m p l).length ≤ l.length) run test_4
-- index out of bounds and failure

-- With context g(l : List Int) t(2 : 3 : α : Type) t(0 : 1 : m : List α) and objects (m.length ≤ l.length ) run test_4
-- fails to unify ; expected ? As would assign tnode lnodes ?


#check 1

-- tracing_mode .std
-- tracing_flags [(`PaInG.embedBackCore, TracingFlags.all)]

-- With context g(l : List Int) and objects ((l.filter (42 == ·)).length ≤ l.length) run test_4

#check List.length_filter_le


-- With context g(α : Type) g(i : BEq α) g(l : List α) and objects ((l.filter (fun x => x == x)).length ≤ l.length) run test_4

-- With context g(l : List Int) u(n : Nat : l.length) and objects ((l.filter (42 == ·)).length ≤ n) run test_4
-- yay ; unode unfolded

-- With context g(l : List Int) u(n : Nat : l.length) t(0 : 1 : m : List Int) and objects ((m.filter (42 == ·)).length ≤ n) run test_4


-- With context g(l : List Int) g(l' : List Int) and objects (l = l') run test_4
-- status 0, ie expected fail ; no matching thm in modules ??

#check List.unzip_cons
#check List.mem_partition


/-
Fix notes
- PaIn → PaInG
- defEqNoMv → defEqWiMv

TODO:
- add uni tests
- add rw tests
- rewriting
- embedProcess
- test embedProcess

-/
