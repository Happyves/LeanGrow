

import LeanGrow.Src.Caching.Query.TestTools


open Lean Meta


#check List

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

-/



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



/-
Todos : at process, maybe make a version of reduce that keeps
the reductions if no progress was made ?? Else, PaIn matching
could fail miserably ?

-/
