
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrowBeta.Caching.NonStrucIndunction

import Mathlib.Data.List.Dedup

set_option linter.style.longLine false


open Lean Meta

-- build with:
-- #eval buildRecursorCache `Mathlib.Data.List.Dedup
-- #eval buildRecursorCache `Mathlib.Data.List.Defs

#eval RecursorCache_printFunIndNames `Mathlib.Data.List.Dedup
#eval RecursorCache_printElimNames `Mathlib.Data.List.Dedup

#eval RecursorCache_printFunIndNames `Mathlib.Data.List.Defs
#eval RecursorCache_printElimNames `Mathlib.Data.List.Defs


-- #eval RecursorCache_printFunIndNamesWithKeys `Mathlib.Data.List.Defs


-- #check List.getLastI.induct
#check List.getLastI.induct_unfolding
