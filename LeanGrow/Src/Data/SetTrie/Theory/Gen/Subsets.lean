

import LeanGrow.Src.Data.SetTrie.Theory.Gen.Gen


variable {n : Nat}


/-

- compute pairwise intersection of family
- for all intersections, for all subsets in intersection,
  lift in family, rec compute settries for pos-family and
  for neg family, map lift on pairs of results
- avoid repeated computation by checking, for all sub in inter,
  if comp (lift & onwards) has already been done by caching
  on lifted subsets ...

-/



partial def UInt8.subsets (x : UInt8) : Array UInt8 :=
  let sz := (7+1)*8 + (6+2)*28 + (5+3)*56 + 4*70 + 8 --expected size via binom
  let A : Array UInt8 := Array.emptyWithCapacity sz
  let rec go (c : UInt8) (A : Array UInt8) : Array UInt8 :=
    if c = x
    then
      let i := x &&& c
      let A := if i != 0 then A.push i else A
      A
    else
      let i := x &&& c
      let A := if i != 0 then A.push i else A
      go (c+1) A
  go 0 A


-- #eval UInt8.subsets 7
-- has duplicates .......
