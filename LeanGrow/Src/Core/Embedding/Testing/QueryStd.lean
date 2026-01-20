

import LeanGrow.Src.Core.Embedding.TestTools_QueryStd


open Lean


#check Int.le_add_one
#check Int.le_add_of_nonneg_left
#check Int.le_add_of_nonneg_right

def testSet_1 := #[``Int.le_add_one, ``Int.le_add_of_nonneg_left, ``Int.le_add_of_nonneg_right]

def test_1 := testSandbox_embedForwIncludeCoreS testSet_1

-- With context g(n : Int) g(m : Int) g(h1 : Int.le 0 n) g(h1 : 0 ≤ m) and objects run test_1
-- fail, due to instances, including 0 as OfNat ??

def test_2 := testSandbox_embedBackMainS testSet_1


-- With context g(n : Int) g(m : Int) and objects (Int.le n (Int.add n m)) run test_2
-- fail



/-
Fix notes
- PaIn → PaInG
- defEqNoMv → defEqWiMv

TODO:
- have testtools reduce with instances and allow to reduce types ?
- fix tests
- add uni tests
- add rw tests
- try cache load tests
- rewriting
- embedProcess
- test embedProcess

-/
