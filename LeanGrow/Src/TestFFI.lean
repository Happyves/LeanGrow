

import LeanGrow.FFI.EETrick

-- #eval eeTrick 3
-- #eval eeTrick 4


-- # UInt32Array

def testUA : UInt32Array :=
  ((UInt32Array.empty).push 2).push 3

def testUA2 : UInt32Array :=
  UInt32Array.mk #[3,2,1]

-- #eval UInt32Array.empty

-- #eval testUA

-- #eval testUA.data

-- #eval testUA2.data

-- #eval testUA2

-- #eval UInt32Array.get! testUA 0
-- #eval UInt32Array.get! testUA 1
-- #eval UInt32Array.get! testUA 2

-- #eval UInt32Array.get! testUA2 0
-- #eval UInt32Array.get! testUA2 1
-- #eval UInt32Array.get! testUA2 2
-- #eval UInt32Array.get! testUA2 3


-- #eval  testUA2.data[0]!
-- #eval  testUA2.data[1]!
-- #eval  testUA2.data[2]!
-- #eval  testUA2.data[3]!

-- #eval testUA.size
-- #eval testUA2.size

-- #eval testUA.set! 0 42
-- #eval testUA2.set! 0 42

-- #eval testUA.oContains 2
-- #eval testUA.oContains 3
-- #eval testUA.oContains 1
-- #eval testUA.oContains 4

-- #eval UInt32Array.empty.oContains 37

-- #eval testUA.binSearch 2
-- #eval testUA.binSearch 3
-- #eval testUA.binSearch 1
-- #eval testUA.binSearch 4

-- #eval UInt32Array.empty.binSearch 37
-- #eval (UInt32Array.empty.push 1).binSearch 37
-- #eval (UInt32Array.empty.push 1).binSearch 1
-- #eval (testUA.push 4).binSearch 37
-- #eval (testUA.push 4).binSearch 4

-- #eval testUA.oInsert 1
-- #eval testUA.oInsert 2
-- #eval testUA.oInsert 3
-- #eval testUA.oInsert 4

-- #eval UInt32Array.empty.oInsert 1

def testMultiRefInsert_1 (a : UInt32Array) : Nat :=
  let fst := (a.oInsert 1).size
  let snd := a.size
  fst + snd

-- #eval testMultiRefInsert_1 testUA
-- #eval testMultiRefInsert_1 .empty


-- #eval testUA.binInsert 1
-- #eval testUA.binInsert 2
-- #eval testUA.binInsert 3
-- #eval testUA.binInsert 4

-- #eval UInt32Array.empty.binInsert 1
-- #eval testUA.binInsert 1 |>.binInsert 5
-- #eval testUA.binInsert 1 |>.binInsert 0
-- #eval testUA.binInsert 1 |>.binInsert 3
-- #eval testUA.binInsert 1 |>.binInsert 2


def testUA3 : UInt32Array :=
  ((UInt32Array.empty).push 1).push 2 |>.push 3 |>.push 4

def testUA4 : UInt32Array :=
  ((UInt32Array.empty).push 4).push 5

-- #eval testUA.hasCommon testUA3
-- #eval testUA3.hasCommon testUA
-- #eval testUA.hasCommon .empty
-- #eval testUA.hasCommon testUA4
-- #eval testUA4.hasCommon testUA

-- #eval testUA.subsetOf testUA3
-- #eval testUA3.subsetOf testUA
-- #eval testUA.subsetOf .empty
-- #eval UInt32Array.empty.subsetOf testUA4
-- #eval testUA3.subsetOf testUA4
-- #eval testUA4.subsetOf testUA3


-- #eval testUA.inter testUA3
-- #eval testUA3.inter testUA
-- #eval testUA.inter .empty
-- #eval testUA.inter testUA4
-- #eval testUA4.inter testUA


-- #eval testUA.union testUA3
-- #eval testUA3.union testUA
-- #eval testUA.union .empty
-- #eval testUA.union testUA4
-- #eval testUA4.union testUA

-- #eval testUA.hasDiff testUA3
-- #eval testUA3.hasDiff testUA
-- #eval testUA.hasDiff .empty
-- #eval testUA.hasDiff testUA4
-- #eval testUA4.hasDiff testUA

-- #eval testUA.diff testUA3
-- #eval testUA3.diff testUA
-- #eval testUA.diff .empty
-- #eval testUA.diff testUA4
-- #eval testUA4.diff testUA

-- #eval UInt32Array.empty.sanitize
-- #eval testUA.sanitize
-- #eval testUA3.sanitize
-- #eval testUA4.sanitize

-- #eval UInt32Array.empty.shiftAdd 42
-- #eval testUA.shiftAdd 42
-- #eval testUA3.shiftAdd 42
-- #eval testUA4.shiftAdd 42

-- #eval UInt32Array.empty.shiftSub 2
-- #eval testUA.shiftSub 2
-- #eval testUA3.shiftSub 2
-- #eval testUA4.shiftSub 2



-- set_option trace.compiler.ir.result true in
def testSpecFoldl (a : UInt32Array) : Nat :=
  a.foldl 0 (fun ui x => if ui == 3 then x+1 else x)

-- #eval testSpecFoldl .empty
-- #eval testSpecFoldl testUA
-- #eval testSpecFoldl testUA3
-- #eval testSpecFoldl testUA4


-- set_option trace.compiler.ir.result true in
def testSpecMap (a : UInt32Array) : UInt32Array :=
  a.map (fun x => x+42)

-- #eval testSpecMap .empty
-- #eval testSpecMap testUA
-- #eval testSpecMap testUA3
-- #eval testSpecMap testUA4
