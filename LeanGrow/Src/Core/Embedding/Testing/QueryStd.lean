

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


-- With context g(n : Int) g(m : Int) and objects (n ≤ (n + m)) run test_2

-- With context g(n : Int) g(m : Int) and objects (n ≤ (m + n)) run test_2

-- With context g(n : Int) g(m : Int) and objects (n ≤ (m + 1)) run test_2

-- With context g(n : Int) g(m : Int) and objects (n ≤ (n + 1)) run test_2


unsafe def test_3_1 := testLoad_embedForwIncludeCoreS #[`Init.Data.List.Basic, `Init.Data.List.Lemmas]


-- With context g(a : List Int) u(b : List Int : [1,2,3]) and objects run test_3_1
-- no lists as sink hyps xox

-- With context g(l : List Int) g(h : l.getLast? = .some 5) and objects run test_3_1

unsafe def test_3_2 := testLoad_embedForwInterCoreS #[`Init.Data.List.Basic, `Init.Data.List.Lemmas]

-- With context g(a : List Int) u(b : List Int : [1,2,3]) and objects run test_3_2


-- With context g(l : List Int) g(h : l.getLast? = .some 5) and objects run test_3_2


unsafe def test_4 := testLoad_embedBackMainS #[`Init.Data.List.Basic, `Init.Data.List.Lemmas]


-- With context g(as : List Int) g(bs : List Int) g(cs : List Int) and objects (as ++ bs ++ cs = as ++ (bs ++ cs)) run test_4

With context g(l : List Int) and objects ((l.filter (42 == ·)).length ≤ l.length) run test_4


#check List.append_assoc
#check List.length_filter_le
#check List.foldl_filter
#check List.foldr_filter
#check List.length_eq_of_beq

#check List.mem_of_getLast?
#check List.mem_of_mem_getLast?

#check List.Pairwise (· < ·)

/-
Fix notes
- PaIn → PaInG
- defEqNoMv → defEqWiMv

TODO:
- bizare matches in last test
- worry about instances : what if thm for abstract instance, and query with
  concrete one ?
- add uni tests
- add rw tests
- try cache load tests
- rewriting
- embedProcess
- test embedProcess

-/
