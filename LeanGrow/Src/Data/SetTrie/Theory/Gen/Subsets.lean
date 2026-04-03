

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
