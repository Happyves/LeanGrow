

import LeanGrow.Src.Caching.Score.ConjecturableProcess


open Lean Meta


def test (n : Name) : MetaM Unit := do
  let .some (.thmInfo I) := (← getEnv).find? n | throwError "Bad name"
  let res ← getConjecturablePos I.type
  IO.println res


#eval test ``Eq.trans

#eval test ``Classical.byCases

#eval test ``Nat.le_trans
