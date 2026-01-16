/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrowBeta.Core.Rewriting.TestTools

import Mathlib.Data.List.Dedup

open List

set_option linter.style.longLine false

open Lean Meta


def testBackRWA := testBackRW `List.dedup_cons_of_mem'

With gnodes (l : List Nat) (P : List Nat → Prop) (h₀ : ∀ a : Nat, a ∈ l.dedup) (h₁ :  P l.dedup) and unodes and tnodes and objects (P (42 :: l).dedup) run testBackRWA
-- Kernel rejects due to mvar, which should be a tnode as fvar, but not handled by `testBackRW` specifically

With gnodes and unodes and tnodes and objects (∀ (l : List Nat) (P : List Nat → Prop) (h₀ : ∀ a : Nat, a ∈ l.dedup) (h₁ :  P l.dedup), P (42 :: l).dedup) run testBackRWA


#check List.dedup_cons_of_mem'
