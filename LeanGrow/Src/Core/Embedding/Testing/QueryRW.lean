

import LeanGrow.Src.Core.Embedding.TestTools_QueryRW


open Lean Meta


unsafe def test_1 := testLoad_embedForwRWMainS #[`Init.Data.List.Basic, `Init.Data.List.Lemmas]

-- With context g(p : Nat → Bool) g(q : Nat → Bool) g(l : List Nat) g(h : ∀ x ∈ l, p x = q x) and objects (List.filter p l = List.filter q l) run test_1
-- List.filter_congr is missing because it has sinks in goal

#check 1
#check List.filter_eq_filterTR
#check List.filterMap_eq_filter
#check List.filter.eq_def
#check List.concat_inj_left
