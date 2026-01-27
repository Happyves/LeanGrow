
import LeanGrow.Src.Caching.Formating.Process

import Mathlib.Data.List.Dedup

open Lean Meta


def test (n : Name) : MetaM Unit := do
  let .some dec := (← getEnv).find? n | throwError "aahh 1"
  let .mk _ thms l1 l2 ← processForCache `dummyMod 42 dec
  thms.foldlM () <| fun badu thm _ => do
    IO.println s!"\nTheorem {thm.name}"
    IO.println s!"Bad uni {repr badu}"
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


def testSpe (n : Name) (badu : badUniType) : MetaM Unit := do
  let .some dec := (← getEnv).find? n | throwError "aahh 1"
  let .mk _ thms l1 l2 ← processForCacheSpe `dummyMod 42 dec badu
  thms.foldlM () <| fun badu thm _ => do
    IO.println s!"\nTheorem {thm.name}"
    IO.println s!"Bad uni {repr badu}"
    match thm with
    | .std _ _ _ _ _ _ goal _ bf bb =>
        IO.println s!"Goal: {← PpExpr goal l1 l2}"
        IO.println s!"Bad forw: {bf}"
        IO.println s!"Bad back: {bb}"
    | .rw .. =>
        IO.println "shouldn't"



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

#check Eq.refl
#eval test `Eq.refl
#eval testSpe `Eq.refl .fwdOnly


#check Iff.refl
#eval test `Iff.refl
#eval testSpe `Iff.refl .fwdOnly
-- not recognized as bad forward though it is ....



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

#check absurd
#eval test `absurd

#check congrArg
#eval test `congrArg

#check congrFun
#eval test `congrFun

#check 1

theorem test_badUni_1 (P : Nat → Prop) (h1 : P 42) (h2: ¬ P 42) : 42 = 37 :=
  absurd h1 h2

#eval test `test_badUni_1

#check 1


theorem test_badUni_2 (P : Nat → Prop) (h1 : P 42) (h2: ¬ P 42) : [1].Pairwise (· ≠ ·) :=
  absurd h1 h2

#eval test `test_badUni_2


#check 1

theorem test_badUni_3 (P : Nat → Prop) (h1 : P 42) (h2: ¬ P 42) : [1].Pairwise (fun x y => P x ∨ P y) :=
  absurd h1 h2

#eval test `test_badUni_3


#check 1

-- To test:
#check Classical.byCases
#check Classical.byContradiction

