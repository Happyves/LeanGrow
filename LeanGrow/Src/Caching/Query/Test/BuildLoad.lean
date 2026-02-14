

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


-- # Stress test

unsafe def loadCachesDoNothing
  (moduleNames : Array Name)
  : MetaM Unit := do
    loadCacheDataS_forTest  moduleNames <| fun data => do
      let test ← data.data.stdBackPaIn.buildAllS (← getLCtx) (← getLocalInstances) [] 0
      return s!"Made it, test build empty : {test == .nil}"

def bigInit := #[`Init.Prelude, `Init.SimpLemmas, `Init.PropLemmas,
                 `Init.Internal.Order.Lemmas, `Init.Data.Nat.Dvd,
                 `Init.Data.Nat.Div.Lemmas, `Init.Data.Subtype.Basic,
                 `Init.Data.Subtype.Order, `Init.Data.List.Perm,
                 `Init.Data.List.Range, `Init.Data.List.Basic, `Init.Data.List.Lemmas]

-- #eval loadCachesDoNothing bigInit
-- no overflow ; acceptably slow without print, and very slow with print
-- heads up : make sure all caches for modules in ↑ were built



-- # Test Loads

-- **Change** capitilized `WithImportModules` in buildPartialCacheData ; check if causes errors

-- #eval exploreCaches_stdBackPaIn_pp #[`Init.Data.List.Perm, `Init.Data.List.Range, `Init.Data.List.Basic, `Init.Data.List.Lemmas]
-- overflow : ue to printing since ↑ stress test passes

-- #eval exploreCaches_stdBackPaIn_pp #[`Init.Data.List.Perm, `Init.Data.List.Range]

-- #eval exploreCaches_stdForwSetTrie_pp #[`Init.Data.List.Basic, `Init.Data.List.Lemmas]

-- #eval exploreCaches_hypIndsOfThm #[`Init.Data.List.Basic, `Init.Data.List.Lemmas] "List.mem_insert_self"

-- #eval exploreCaches_thms #[`Init.Data.List.Basic, `Init.Data.List.Lemmas]

-- #eval exploreCaches_stdForwSetTrie_pp #[`Init.Data.List.Perm, `Init.Data.List.Range, `Init.Data.List.Basic, `Init.Data.List.Lemmas]
