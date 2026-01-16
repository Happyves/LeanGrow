
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrowBeta.Core.Induction.TestTools

import Mathlib.Data.List.Dedup
-- We require the import because the elaboration in the `With gnodes ..` command needs it !
import Mathlib.Data.List.Defs

-- #exit

set_option linter.style.longLine false

unsafe def testGoalInductionA := testGoalInduction `Mathlib.Data.List.Dedup

-- With gnodes (n : Nat) (hn : n = 42) and unodes and tnodes and objects (n % 2 = 0) run testGoalInductionA

-- With gnodes (l : List Nat) (hn : l.dedup = [42]) and unodes and tnodes and objects (l = 42 :: l) run testGoalInductionA

-- With gnodes (l : List Nat) (hn : l.dedup = [42]) and unodes and tnodes and objects ((fun x => l = x :: l) 42) run testGoalInductionA


unsafe def testSndHyp := testHypInduction `Mathlib.Data.List.Dedup 1

-- With gnodes (l : List Nat) (hn : l = [42] ∨ l = [37]) and unodes and tnodes and objects (l.dedup = l) run testSndHyp

-- With gnodes (l : List Nat) (hn : l = [42] ∧ l = [37]) and unodes and tnodes and objects (l.dedup = l) run testSndHyp

-- With gnodes (l : List Nat) (hn : ∃ n, l = [n]) and unodes and tnodes and objects (l.dedup = l) run testSndHyp

--negative test
-- With gnodes (l : List Nat) (hn : l.dedup = [42]) and unodes and tnodes and objects ((fun x => l = x :: l) 42) run testSndHyp


unsafe def testThirdHyp := testHypInduction `Mathlib.Data.List.Dedup 2

-- With gnodes (n : Nat) (m : Nat) (hn : n ≤ m) and unodes and tnodes and objects (n % 2 = m) run testThirdHyp

-- With gnodes (n : Nat) (m : Nat) (hn : Nat.le n m) and unodes and tnodes and objects (n % 2 = m) run testThirdHyp

-- With gnodes (l : List Nat) (L : List Nat) (hn : l.Perm L) and unodes and tnodes and objects (l.dedup = l) run testThirdHyp

-- With gnodes (l : List Nat) (L : List Nat) (hn : (fun x => l.Perm x) L) and unodes and tnodes and objects (l.dedup = l) run testThirdHyp

-- negative test
-- With gnodes (l : List Nat) (L : List Nat) (hn : l.Perm L) and unodes and tnodes and objects (l.dedup = l) run testSndHyp


unsafe def testGoalInductionB := testGoalInduction `Mathlib.Data.List.Defs

-- tracing_mode .std
-- tracing_flags [(`functionalInductionMain,TracingFlags.all)]

-- With gnodes (l : List Nat) (hn : l.dedup = [42]) and unodes and tnodes and objects (l.getLastI = 42) run testGoalInductionB


unsafe def testSndHypB := testHypInduction `Mathlib.Data.List.Defs 1

-- With gnodes (l : List Nat) (hn : l.getLastI = 42) and unodes and tnodes and objects (l.dedup = [42]) run testSndHypB


#check 1

open Lean Meta

#check List.getLastI.induct

unsafe def testGoalInductionC := testGoalInductionMulti #[`Mathlib.Data.List.Dedup]


-- negative test
-- With gnodes (n : Nat) (hn : n = 42) and unodes (m : Nat : n+2) and tnodes and objects (m % 2 = 0) run testGoalInductionA


-- With gnodes (n : Nat) (hn : n = 42) and unodes (m : Nat : n+2) and tnodes and objects ((n+m) % 2 = 0) run testGoalInductionA

#check 1

-- With gnodes (n : Nat) (hn : n = 42) and unodes (m : Nat : n+2) and tnodes and objects ((n+m) % 2 = 0) run testGoalInductionC


#check 1

-- With gnodes (l : List Nat) (hn : l.dedup = [42]) and unodes (L : List Nat : 37 :: l) and tnodes and objects (l.getLastI = L.getLastI) run testGoalInductionB

#check 1

#check List.get

-- With gnodes (l : List Nat) (hn : l.dedup = [42]) and unodes and tnodes (L : List Nat) and objects (L = l) run testGoalInductionA


#check 1

-- With gnodes (l : List Nat) (hn : l.dedup = [42]) (n : Nat) and unodes and tnodes (hf : n < l.length) and objects (l.get ⟨n,hf⟩ = 37) run testGoalInductionA

#check 1
