
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrowBeta.Caching.TestTools

import Mathlib.Data.List.Dedup
import Mathlib.Data.List.DropRight



open Lean Meta


-- In ↓, remember to manually delete cache before, as `buildPartialCacheDataS` will build on top of it otherwise
-- #eval buildPartialCacheDataS #[`Mathlib.Data.List.Dedup] 10
-- Latest: 6 times


-- #eval buildCacheDataS #[`Mathlib.Data.List.Dedup]
-- currently fails with unknown metavariable issue

-- #eval exploreCaches_ThmHypInds false #[`Mathlib.Data.List.Dedup]
