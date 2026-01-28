

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
-- buuuuugs


-- With context g(l : List Int) g(l' : List Int) g(h : l ++ l' ≠ []) and objects run test_3_2
-- bug


#check List.append_ne_nil_of_left_ne_nil
#check List.append_ne_nil_of_right_ne_nil
#check List.exists_mem_of_ne_nil
#check List.head_mem
#check List.getLast_mem
#check List.exists_cons_of_ne_nil


unsafe def test_4 := testLoad_embedBackMainS #[`Init.Data.List.Basic, `Init.Data.List.Lemmas]


-- With context g(as : List Int) g(bs : List Int) g(cs : List Int) and objects (as ++ bs ++ cs = as ++ (bs ++ cs)) run test_4

#check List.append_assoc


-- tracing_mode .std
-- tracing_flags [(`PaInG.embedBackCore, TracingFlags.all)]

-- With context g(l : List Int) and objects ((l.filter (42 == ·)).length ≤ l.length) run test_4

-- With context g(α : Type) g(i : BEq α) g(l : List α) and objects ((l.filter (fun x => x == x)).length ≤ l.length) run test_4


#check List.length_filter_le

-- With context g(l : List Int) g(l' : List Int) and objects (l = l') run test_4
-- buuuuuuug


#check List.beq_cons_nil
#check List.findSome?_cons
#check List.set.eq_def

/-
Fix notes
- PaIn → PaInG
- defEqNoMv → defEqWiMv

TODO:
- duplication in embedForwIncludeCore
- bugs here
- test embedBackMainS with tnodes and unodes
- add uni tests
- add rw tests
- try cache load tests
- rewriting
- embedProcess
- test embedProcess

-/
