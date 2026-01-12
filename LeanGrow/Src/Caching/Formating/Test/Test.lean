
import LeanGrow.Src.Caching.Formating.Process

import Mathlib.Data.List.Dedup

open Lean Meta


def test (n : Name) : MetaM Unit := do
  let .some dec := (← getEnv).find? n | throwError "aahh 1"
  let .mk _ thms l1 l2 ← processForCache `dummyMod 42 dec
  for thm in thms do
    IO.println s!"\nTheorem {thm.name}"
    match thm with
    | .std _ _ _ _ _ _ goal _ bf bb =>
        IO.println s!"Goal: {← PpExpr goal l1 l2}"
        IO.println s!"Bad forw: {bf}"
        IO.println s!"Bad back: {bb}"
    | .rw _ _ _ goal rep _ _ _ _ bf bb si =>
        IO.println s!"RW goal: {← PpExpr goal l1 l2}"
        IO.println s!"RW rep: {← PpExpr rep l1 l2}"
        IO.println s!"Simplifier score: {si}"
        IO.println s!"Bad forw: {bf}"
        IO.println s!"Bad back: {bb}"



#check if_pos
#eval test `if_pos

#check dif_pos
#eval test `dif_pos

#check List.dedup_idem
#eval test `List.dedup_idem

#check Nat.add_zero
#eval test `Nat.add_zero

#check Nat.zero_add
#eval test `Nat.zero_add

#check Nat.add_succ
#eval test `Nat.add_succ

#check Nat.succ_add
#eval test `Nat.succ_add

#check Nat.add_comm
#eval test `Nat.add_comm

-- tracing_mode .std
-- tracing_flags [(`simplifierScoreCore, TracingFlags.all)]

#check List.getElem_map
#eval test `List.getElem_map


#check List.length_map
#eval test `List.length_map

#check Nat.le_or_eq_of_le_succ
#eval test `Nat.le_or_eq_of_le_succ

#check Nat.lt_or_gt_of_ne
#eval test `Nat.lt_or_gt_of_ne

#check Nat.ne_iff_lt_or_gt
#eval test `Nat.ne_iff_lt_or_gt

#check Int.le_add_one
#eval test `Int.le_add_one

#check Eq.trans
#eval test `Eq.trans

#check Eq.symm
#eval test `Eq.symm

#check le_trans
#eval test `le_trans

#check List.getElem_cons
#eval test `List.getElem_cons

-- tracing_mode .std
-- tracing_flags [(`isBadForBackRW, TracingFlags.all),
--                (`isBadForForwRW, TracingFlags.all),
--                (`isBadForRW, TracingFlags.all),
--                (`isGoodForRW, TracingFlags.all),
--                ]


#check List.getElem_cons_succ
#eval test `List.getElem_cons_succ
-- is bad because defeq via to iota after instance reduction and List.get delta
#check List.get

#check List.getElem_cons_zero
#eval test `List.getElem_cons_zero
