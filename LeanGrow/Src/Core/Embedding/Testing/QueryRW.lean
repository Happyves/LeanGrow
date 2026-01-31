

import LeanGrow.Src.Core.Embedding.TestTools_QueryRW


open Lean Meta


unsafe def test_1 := testLoad_embedForwRWMainS #[`Init.Data.List.Basic, `Init.Data.List.Lemmas]

unsafe def test_2 := testLoad_embedBackRWMainnS #[`Init.Data.List.Basic, `Init.Data.List.Lemmas]


-- With context g(p : Nat → Bool) g(q : Nat → Bool) g(l : List Nat) g(h : ∀ x ∈ l, p x = q x) and objects (List.filter p l = List.filter q l) run test_1
-- List.filter_congr is missing because it has sinks in goal

-- With context g(p : Nat → Bool) g(q : Nat → Bool) g(l : List Nat) g(h : ∀ x ∈ l, p x = q x) and objects (List.filter p l = List.filter q l) run test_2
-- bug : missing filter_eq_filterTR and filter_congr

#check 1
#check List.filter_eq_filterTR
#check List.filterMap_eq_filter
#check List.filter.eq_def
#check List.concat_inj_left
#check List.filter_congr


def test_3 := testSandbox_embedForwRWMainS #[`Nat.add_comm]

def test_4 := testSandbox_embedBackRWMainnS #[`Nat.add_comm]


-- With context g(n : Nat) g(m : Nat) and objects (n + m = 42) run test_3

-- With context g(n : Nat) g(m : Nat) and objects (n + m = 42) run test_4


-- With context g(n : Nat) g(m : Nat) and objects (∃ x : Fin (n+m), x.val = 42) run test_3

-- With context g(n : Nat) g(m : Nat) and objects (∃ x : Fin (n+m), x.val = 42) run test_4

-- With context g(n : Nat) g(m : Nat) and objects (∀  x : Fin (n+m), x.val = 42) run test_3
-- binder ignored as desired

-- With context g(n : Nat) g(m : Nat) and objects (∀  x : Fin (n+m), x.val = 42) run test_4

-- With context g(n : Nat) g(m : Nat) g(y : Fin (m+n)) and objects (∃ x : Fin (n+m), x = .mk y.val (by rw [ show n + m = m + n from by apply Nat.add_comm] ; exact y.isLt)) run test_3
-- correct, and occurence in proof is ignored as desired

-- With context g(n : Nat) g(m : Nat) g(y : Fin (m+n)) and objects (∃ x : Fin (n+m), x = .mk y.val (by rw [ show n + m = m + n from by apply Nat.add_comm] ; exact y.isLt)) run test_4

-- With context g(n : Nat) g(m : Nat) g(y : Fin (n+m)) and objects ((fun z : Fin (n+m) => 42) (Fin.mk y.val y.isLt) = 42) run test_3
-- would cause problems is inreduced, but we reduce queries

def test_5 := testSandbox_embedBackRWMainnS #[`List.concat_inj_left]

-- With context g(l : List Nat) t(0 : 0: m : Nat) and objects (l.concat m = l.concat 42) run test_5


-- Todo : print only dirs at back, currently has workers too


#check mkProjFn

#check getStructureFields


/-
Todo:
- test rw under binders
- find out if appearance of proj function is due to reduction with reducible transparency
- better management of projections from the start ?

LG:
- add option to sample hyps of forward sample, and should be used for
  conveyorbelt of type goal-hyp, rather then thm,
- test conjecturables-sampling

-/
