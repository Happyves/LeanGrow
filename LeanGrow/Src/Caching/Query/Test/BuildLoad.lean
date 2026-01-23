

import LeanGrow.Src.Caching.Query.TestTools


open Lean Meta


#check List




-- #eval buildPartialCacheDataFullS `Init.Prelude

-- #eval buildCacheDataS `Init.Prelude

-- #eval exploreCaches_thms #[`Init.Prelude]

-- #eval exploreCaches_stdBackPaIn_pp #[`Init.Prelude]

-- #eval exploreCaches_stdForwSetTrie_pp #[`Init.Prelude]






-- #eval buildPartialCacheDataFullS `Init.PropLemmas

-- #eval buildCacheDataS `Init.PropLemmas

-- #eval exploreCaches_thms #[`Init.PropLemmas]

-- #eval exploreCaches_stdBackPaIn_pp #[`Init.PropLemmas]

-- #eval exploreCaches_stdForwSetTrie_pp #[`Init.PropLemmas]



-- #eval exploreCaches_stdBackPaIn_pp #[`Init.PropLemmas, `Init.Prelude]

-- #eval exploreCaches_stdForwSetTrie_pp #[`Init.PropLemmas, `Init.Prelude]





-- # Test builds

/-
- Init.Prelude
- Init.SimpLemmas
- Init.PropLemmas
- Init.Internal.Order.Lemmas
- Init.Data.Nat.Dvd
- Init.Data.Nat.Div.Lemmas
- Init.Data.Subtype.Basic
- Init.Data.Subtype.Order
- Init.Data.List.Perm
- Init.Data.List.Range
- Init.Data.List.Basic
- Init.Data.List.Lemmas

-/



-- #eval buildPartialCacheDataFullS `Init.Prelude

-- #eval buildCacheDataS `Init.Prelude


-- #eval buildPartialCacheDataFullS `Init.SimpLemmas

-- #eval buildCacheDataS `Init.SimpLemmas


-- #eval buildPartialCacheDataFullS `Init.PropLemmas

-- #eval buildCacheDataS `Init.PropLemmas


-- #eval buildPartialCacheDataFullS `Init.Internal.Order.Lemmas

-- #eval buildCacheDataS `Init.Internal.Order.Lemmas


-- #eval buildPartialCacheDataFullS `Init.Data.Nat.Dvd

-- #eval buildCacheDataS `Init.Data.Nat.Dvd


-- #eval buildPartialCacheDataFullS `Init.Data.Nat.Div.Lemmas

-- #eval buildCacheDataS `Init.Data.Nat.Div.Lemmas


-- #eval buildPartialCacheDataFullS `Init.Data.Subtype.Basic

-- #eval buildCacheDataS `Init.Data.Subtype.Basic


-- #eval buildPartialCacheDataFullS `Init.Data.Subtype.Order

-- #eval buildCacheDataS `Init.Data.Subtype.Order


-- #eval buildPartialCacheDataFullS `Init.Data.List.Perm

-- #eval buildCacheDataS `Init.Data.List.Perm


-- #eval buildPartialCacheDataFullS `Init.Data.List.Range

-- #eval buildCacheDataS `Init.Data.List.Range


-- #eval buildPartialCacheDataFullS `Init.Data.List.Basic

-- #eval buildCacheDataS `Init.Data.List.Basic


-- #eval buildPartialCacheDataFullS `Init.Data.List.Lemmas

-- #eval buildCacheDataS `Init.Data.List.Lemmas




-- # Test Loads


-- #eval exploreCaches_stdBackPaIn_pp #[`Init.Data.List.Perm, `Init.Data.List.Range, `Init.Data.List.Basic, `Init.Data.List.Lemmas]
-- overflow XD probably due to printing ?

-- #eval exploreCaches_stdBackPaIn_pp #[`Init.Data.List.Perm, `Init.Data.List.Range]
-- buggy merge again: LLE at Init.Data.List.Range.41.2

-- #eval exploreCaches_stdForwSetTrie_pp #[`Init.Data.List.Perm, `Init.Data.List.Range, `Init.Data.List.Basic, `Init.Data.List.Lemmas]
