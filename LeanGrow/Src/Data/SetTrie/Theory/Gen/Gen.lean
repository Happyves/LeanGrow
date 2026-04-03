


import LeanGrow.Src.Data.SetTrie.Operations



structure ByteVect_8x (n : Nat) where
  a : ByteArray
  hs : a.size = n

instance (n : Nat) : Inhabited (ByteVect_8x n) where
  default := .mk (.mk (Array.replicate n 0)) (by dsimp [ByteArray.size] ; apply Array.size_replicate)


@[inline]
def UInt8.asNatArray (off : Nat) (x : UInt8) : Array Nat :=
  let c := 0
  let one : UInt8 := 1
  let One : Bool := (one.land x) != 0
  let c := if One then c+1 else c
  let two : UInt8 := 2
  let Two : Bool := (two.land x) != 0
  let c := if Two then c+1 else c
  let three : UInt8 := 4
  let Three : Bool := (three.land x) != 0
  let c := if Three then c+1 else c
  let four : UInt8 := 8
  let Four : Bool := (four.land x) != 0
  let c := if Four then c+1 else c
  let five : UInt8 := 16
  let Five : Bool := (five.land x) != 0
  let c := if Five then c+1 else c
  let six : UInt8 := 32
  let Six : Bool := (six.land x) != 0
  let c := if Six then c+1 else c
  let seven : UInt8 := 64
  let Seven : Bool := (seven.land x) != 0
  let c := if Seven then c+1 else c
  let eight : UInt8 := 128
  let Eight : Bool := (eight.land x) != 0
  let c := if Eight then c+1 else c
  let A : Array Nat := Array.emptyWithCapacity c
  let v := off
  let A := if One then A.push v else A
  let v := v+1
  let A := if Two then A.push v else A
  let v := v+1
  let A := if Three then A.push v else A
  let v := v+1
  let A := if Four then A.push v else A
  let v := v+1
  let A := if Five then A.push v else A
  let v := v+1
  let A := if Six then A.push v else A
  let v := v+1
  let A := if Seven then A.push v else A
  let v := v+1
  let A := if Eight then A.push v else A
  A

@[inline]
def ByteArray.asNatArray (a : ByteArray) : Array Nat :=
  let A := a.data--mapIdx UInt8.asNatArray
  let s := A.size
  let rec go (i off : Nat) (R : Array (Array Nat)) : Array (Array Nat) :=
    if i < s
    then
      let R := R.push <| A[i]!.asNatArray off
      go (i+1) (off+8) R
    else
      R
  let A := go 0 0 (Array.emptyWithCapacity s)
  A.flatten


instance (n : Nat) : ToString (ByteVect_8x n) where
  toString := fun a => toString a.a.asNatArray

@[inline]
unsafe def IO.randBV_impl (n : Nat) : IO (ByteVect_8x n) := do
  let src ← IO.getRandomBytes n.toUSize
  return .mk src lcProof

@[inline, implemented_by IO.randBV_impl]
def IO.randBV (n : Nat) : IO (ByteVect_8x n) := do
  return default

#check 1

@[inline] -- should be given better support with FFI
def ByteVect_8x.bytewise {n : Nat} (x y : ByteVect_8x n)
  (f: UInt8 → UInt8 → UInt8) : ByteVect_8x n :=
  let A : Array UInt8 := Array.emptyWithCapacity n
  let rec go (i : Nat) (A : Array UInt8) (hi : A.size = i) (spe : i ≤ n) : ByteVect_8x n :=
    if h : i < n
    then
      let a := x.a[i]!
      let b := y.a[i]!
      let res := f a b
      let A := A.push res
      go (i+1) A (by grind) (by grind)
    else
      .mk (.mk A) (by dsimp [ByteArray.size] ; grind)
  go 0 A (by grind) (Nat.zero_le _)

#check 1

@[inline]
def ByteVect_8x.or {n : Nat} (x y : ByteVect_8x n) :=
  ByteVect_8x.bytewise x y UInt8.lor


@[inline]
def ByteVect_8x.and {n : Nat} (x y : ByteVect_8x n) :=
  ByteVect_8x.bytewise x y UInt8.land

instance (n : Nat) : BEq (ByteVect_8x n) where
  beq := fun x y => x.a == y.a

@[inline]
def ByteVect_8x.sub {n : Nat} (x y : ByteVect_8x n) : Bool :=
  x.and y == x


@[inline]
def UInt8.count (x : UInt8) : Nat :=
  let c := 0
  let one : UInt8 := 1
  let One : Bool := (one.land x) != 0
  let c := if One then c+1 else c
  let two : UInt8 := 2
  let Two : Bool := (two.land x) != 0
  let c := if Two then c+1 else c
  let three : UInt8 := 4
  let Three : Bool := (three.land x) != 0
  let c := if Three then c+1 else c
  let four : UInt8 := 8
  let Four : Bool := (four.land x) != 0
  let c := if Four then c+1 else c
  let five : UInt8 := 16
  let Five : Bool := (five.land x) != 0
  let c := if Five then c+1 else c
  let six : UInt8 := 32
  let Six : Bool := (six.land x) != 0
  let c := if Six then c+1 else c
  let seven : UInt8 := 64
  let Seven : Bool := (seven.land x) != 0
  let c := if Seven then c+1 else c
  let eight : UInt8 := 128
  let Eight : Bool := (eight.land x) != 0
  let c := if Eight then c+1 else c
  c

@[inline]
def ByteVect_8x.count {n : Nat} (x : ByteVect_8x n) : Nat :=
  x.a.foldl (fun s u => u.count + s) 0


#exit


-- #eval IO.randBV 5

-- #eval IO.randBV 5

-- #eval IO.randBV 5

-- #eval IO.randBV 5


#eval IO.randBV 1

#eval IO.randBV 1

#eval IO.randBV 1

#eval IO.randBV 1


#check 1


def testbinom : IO Unit := do
  let mut ls := Array.replicate 8 0
  for _ in Array.range 32 do
    let sample ← IO.randBV 1
    let l := sample.a.asNatArray.size
    ls := ls.modify l Nat.succ
  let res := ls.map (fun x => x.toFloat / 32)
  IO.println res


-- #eval testbinom
-- #eval testbinom
-- #eval testbinom

def testbinom' : IO Unit := do
  let mut ls := Array.replicate 8 0
  for _ in Array.range 256 do
    let sample ← IO.randBV 1
    let l := sample.a.asNatArray.size
    ls := ls.modify l Nat.succ
  for n in ls do
    for _ in Array.range n do
      IO.print "x"
    IO.println ""

#eval testbinom'
#eval testbinom'
#eval testbinom'


def testbinom'' : IO Unit := do
  let mut ls := Array.replicate 32 0
  for _ in Array.range 500 do
    let sample ← IO.randBV 3
    let l := sample.a.asNatArray.size
    ls := ls.modify l Nat.succ
  for n in ls do
    for _ in Array.range n do
      IO.print "x"
    IO.println ""

-- #eval testbinom''
