
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Lean.Data.Name
import Lean.AuxRecursor

open Lean Name


def recSuffix := "rec"

namespace Lean.Name

/--
Based on Loogles blacklisting.

Refer to `Lean.Name.isInternalDetail` to keep in sync.
For example, from 4.18 to 4.19 "proof_"
-/
def blackListCaching : Name → Bool
  | .str p s     =>
    s.startsWith "_"
    -- **Watch out with ↑** : in case `eq` and `proof` become internal in the future
      -- `|| matchPrefix s "eq_"` we want them
      || matchPrefix s "match_" -- blacklist, since we'll use functional induction instead
      -- `|| matchPrefix s "proof_"` we want them
      || p.blackListCaching -- we have to recurse to avoid wierd decls like `_private.0.List.permutationsAux2.match_2.splitter`
      -- Wrt. ↓, they don't show up in env constants anyway
      -- || s == recSuffix
      -- || s == casesOnSuffix
      -- || s == recOnSuffix
      -- || s == brecOnSuffix
  | .num _ _     => true
  | p            => p.isInternalOrNum
where
  /-- Check that a string begins with the given prefix, and then is only digit characters. -/
  matchPrefix (s : String) (pre : String) :=
    s.startsWith pre && (s |>.drop pre.length |>.all Char.isDigit)
