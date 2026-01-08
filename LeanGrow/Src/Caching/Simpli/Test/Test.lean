
import LeanGrow.Src.Caching.Formating.Process
import LeanGrow.Src.Caching.Simpli.Main

import Mathlib.Data.List.Dedup

open Lean Meta


def test (n : Name) (ratio : Float) : MetaM Unit := do
  let .some dec := (← getEnv).find? n | throwError "aahh 1"
  let (_,thms) ← processForCache `dummyMod 42 dec
  for thm in thms do
    IO.println s!"Pathological: {thm.pathologicalMvarApp?}\n"
    match thm with
    | .std _ _ _ hyps mc _ goal sinks =>
        withOptions (fun op =>
          Lean.Option.set op ⟨`trace.Meta.isDefEq,true⟩ true
          )
          do
          let res ←  isBadForBack `dummyMod 42 sinks hyps goal
          IO.println s!"Bad back: {res}\n"
        let res ←  isBadForForw sinks hyps goal mc
        -- had to come second as it didn't clear assignement and insatnciated ...
        IO.println s!"Bad forw: {res}"
    | .rw _ _ _ goal rep hyps _ _ sinks =>
        IO.println s!"RW goal: {← ppExpr goal}"
        IO.println s!"RW rep: {← ppExpr rep}"
        let .mk res _ _ ←  isSimplifierCond {} {} goal rep
        IO.println s!"Cond: {res}"
        let .mk res _ _ ←  isSimplifierCondFuzz ratio {} {} goal rep
        IO.println s!"Cond fuzz: {res}\n"
        let r ← isBadForBackRW `dummyMod 42 sinks hyps goal rep
        IO.println s!"Bad back: {r}\n"



#eval test `if_pos 0.5
#eval test `dif_pos 0.5
#eval test `List.dedup_idem 0.5
#eval test `Nat.add_zero 0.5
#eval test `Nat.add_comm 0.5
#eval test `List.getElem_map 0.5
#eval test `List.length_map 0.5


#check Nat.le_or_eq_of_le_succ
#check Nat.lt_or_gt_of_ne
#check Nat.ne_iff_lt_or_gt

#eval test `Nat.le_or_eq_of_le_succ 0.5
#eval test `Nat.lt_or_gt_of_ne 0.5
#eval test `Nat.ne_iff_lt_or_gt 0.5
#eval test `Nat.ne_iff_lt_or_gt 0.75
#eval test `Nat.ne_iff_lt_or_gt 0.9


#check if_pos


#eval test ``Int.le_add_one 0.5
-- DBG : the sink is really wierd and shouldn't have any dup nor the + 1 ...
-- Back is true but we don't want it to be ...
-- Maybe, for back fvarify mvars of hyps and keep goal mvars, and for
-- forw, fvarify goal mvars, and then test defeq



#eval test `Eq.trans 0.5
-- won't apply as backstep anyway, since a rw


#check le_trans


#eval test `le_trans 0.5
-- bad back identified
-- requied the eq up to mvar casue defeq failed ....

#check 1

#check Lean.Option

-- #eval Lean.getOptionDescr `trace.Meta.isDefEq


#check Meta.Context
