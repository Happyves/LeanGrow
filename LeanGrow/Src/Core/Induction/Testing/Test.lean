
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Core.Induction.TestTools

import Mathlib.Data.List.Dedup
-- We require the import because the elaboration in the `With context ..` command needs it !
import Mathlib.Data.List.Defs

-- #exit

set_option linter.style.longLine false

def testGoalInductionA := testGoalInduction `Mathlib.Data.List.Dedup

-- With context g(n : Nat) g(hn : n = 42) and objects (n % 2 = 0) run testGoalInductionA

-- With context g(n : Nat) u(hn : n = 42 : sorry) and objects (n % 2 = 0) run testGoalInductionA
-- remeber that proof valued us will become gnodes

-- With context g(l : List Nat) g(hn : l.dedup = [42]) and objects (l = 42 :: l) run testGoalInductionA

-- With context g(l : List Nat) g(hn : l.dedup = [42]) and objects ((fun x => l = x :: l) 42) run testGoalInductionA


def testSndHyp := testHypInduction `Mathlib.Data.List.Dedup 1

-- With context g(l : List Nat) g(hn : l = [42] ∨ l = [37]) and  objects (l.dedup = l) run testSndHyp

-- With context g(l : List Nat) g(hn : l = [42] ∧ l = [37]) and  objects (l.dedup = l) run testSndHyp

-- With context g(l : List Nat) g(hn : ∃ n, l = [n]) and  objects (l.dedup = l) run testSndHyp

--negative test
-- With context g(l : List Nat) g(hn : l.dedup = [42]) and  objects ((fun x => l = x :: l) 42) run testSndHyp


def testThirdHyp := testHypInduction `Mathlib.Data.List.Dedup 2

-- With context g(n : Nat) g(m : Nat) g(hn : n ≤ m) and  objects (n % 2 = m) run testThirdHyp

-- With context g(n : Nat) g(m : Nat) g(hn : Nat.le n m) and  objects (n % 2 = m) run testThirdHyp

-- With context g(l : List Nat) g(L : List Nat) g(hn : l.Perm L) and  objects (l.dedup = l) run testThirdHyp

-- With context g(l : List Nat) g(L : List Nat) g(hn : (fun x => l.Perm x) L) and  objects (l.dedup = l) run testThirdHyp

-- negative test
-- With context g(l : List Nat) g(L : List Nat) g(hn : l.Perm L) and  objects (l.dedup = l) run testSndHyp


def testGoalInductionB := testGoalInduction `Mathlib.Data.List.Defs

-- With context g(l : List Nat) g(hn : l.dedup = [42]) and objects (l.getLastI = 42) run testGoalInductionB

#check List.permutationsAux.rec
-- has 2 majors, which we don't support ...


def testSndHypB := testHypInduction `Mathlib.Data.List.Defs 1

-- With context g(l : List Nat) g(hn : l.getLastI = 42) and objects (l.dedup = [42]) run testSndHypB


-- negative test
-- With context g(n : Nat) g(hn : n = 42) u(m : Nat : n+2) and objects (m % 2 = 0) run testGoalInductionA


-- With context g(n : Nat) g(hn : n = 42) u(m : Nat : n+2) and objects ((n+m) % 2 = 0) run testGoalInductionA


-- With context g(l : List Nat) g(hn : l.dedup = [42]) u(L : List Nat : 37 :: l) and objects (l.getLastI = L.getLastI) run testGoalInductionB


#check List.get

-- negative : no tnodes in induct hyp, only for structures
-- With context g(l : List Nat) g(hn : l.dedup = [42]) t(37 : 67 : L : List Nat) and objects (L = l) run testGoalInductionA

-- With context g(l : List Nat) u(hn : l.dedup = [42] : sorry) g(n : Nat) t(37 : 67 : hf : n < l.length) and objects (l.get ⟨n,hf⟩ = 37) run testGoalInductionA
