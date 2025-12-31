

/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrowBeta.Utils.Std.PersistentHashMap

open Lean


def Lean.PersistentHashMap.testIns : @PersistentHashMap UInt64 Nat _ ⟨(fun x => x%2)⟩ → UInt64 → Nat → @PersistentHashMap UInt64 Nat _ ⟨(fun x => x%2)⟩ :=
  @PersistentHashMap.insert UInt64 Nat _ ⟨(fun x => x%2)⟩


def testPHM := ((((PersistentHashMap.testIns default 1 42).testIns 2 43).testIns 2 44).testIns 3 45).testIns 4 46

#eval testPHM.toArray


#eval (testPHM.update 1 (fun x => x + 37)).toArray
#eval (testPHM.update 2 (fun x => x + 37)).toArray
#eval (testPHM.update 3 (fun x => x + 37)).toArray
#eval (testPHM.update 4 (fun x => x + 37)).toArray
#eval (testPHM.update 5 (fun x => x + 37)).toArray
#eval (testPHM.update 0 (fun x => x + 37)).toArray

#eval testPHM.print


def testPHM2 := ((((PersistentHashMap.testIns default 1 42).testIns 2 43)).testIns 3 45)

#eval testPHM2.print

#eval (testPHM2.update 1 (fun x => x + 37)).toArray
#eval (testPHM2.update 2 (fun x => x + 37)).toArray
#eval (testPHM2.update 3 (fun x => x + 37)).toArray
#eval (testPHM2.update 4 (fun x => x + 37)).toArray
