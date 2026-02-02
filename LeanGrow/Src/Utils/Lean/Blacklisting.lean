
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Lean.Data.Name
import Lean.AuxRecursor

import Lean.Meta.Tactic.FunInd

open Lean Name


def recSuffix := "rec"

namespace Lean.Name

/--
Based on Loogle's blacklisting.

Refer to `Lean.Name.isInternalDetail` to keep in sync.
For example, from 4.18 to 4.19 "proof_"
-/
def blackListCachingCore : Name → Bool
  | .str p s     =>
    s.startsWith "_"
      -- || matchPrefix s "eq_"
      || matchPrefix s "match_"
      -- || matchPrefix s "proof_"
      || matchPrefix s "omega_"
      || p.isInternalOrNum
      || s == "below"
  | .num _ _     => true
  | p            => p.isInternalOrNum
where
  /-- Check that a string begins with the given prefix, and then is only digits/'_'. -/
  matchPrefix (s : String) (pre : String) :=
    s.startsWith pre && (s |>.drop pre.length |>.all fun c => c.isDigit || c == '_')



#check Lean.Name.isInternalDetail
#check Lean.isNoConfusion


def blackListCaching (env : Environment) (n : Name) : Bool :=
  (noConfusionExt.isTagged env n) || blackListCachingCore n


def blackListSampleDelta : Name → Bool
  | .str p s     =>
    s.startsWith "_"
      || matchPrefix s "eq_"
      || matchPrefix s "match_" -- blacklist, since we'll use functional induction instead
      || matchPrefix s "proof_"
      || s == "noConfusion"
      || s == "induct_unfolding"
      || s == "induct"
      || s == "fun_cases_unfolding"
      || s == "fun_cases"
      || s == "mutual_induct_unfolding"
      || s == "mutual_induct"
      || s == recSuffix
      || s == casesOnSuffix
      || s == recOnSuffix
      || s == brecOnSuffix
      || p.blackListSampleDelta -- we have to recurse to avoid wierd decls like `_private.0.List.permutationsAux2.match_2.splitter`

  | .num _ _     => true
  | p            => p.isInternalOrNum
where
  /-- Check that a string begins with the given prefix, and then is only digit characters. -/
  matchPrefix (s : String) (pre : String) :=
    s.startsWith pre && (s |>.drop pre.length |>.all Char.isDigit)

-- compare to
#check Meta.getFunIndInfo?
