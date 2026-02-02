
import LeanGrow.Src.SampleGenScore.Delab.ContraExFalso

import Mathlib.Data.List.Dedup

set_option linter.style.longLine false

open Lean Meta


def test_exfalso_sample (n : Name) : MetaM Unit := do
  let .some info := (← getEnv).find? n | throwError "Bad name"
  lambdaTelescope info.value! <| fun _ b => do
    let h := b.getAppFn'
    let as := b.getAppArgs
    let sub ← delabSample_ExFalso_core h as
    match sub with
    | .none => IO.println "Not contradiction"
    | .some nex =>
        IO.println s!"Type: {← ppExpr (← inferType nex)}\nTerm: {← ppExpr ( nex)}"



def test_contra_sample (n : Name) : MetaM Unit := do
  let .some info := (← getEnv).find? n | throwError "Bad name"
  lambdaTelescope info.value! <| fun _ b => do
    let h := b.getAppFn'
    let as := b.getAppArgs
    let sub ← delabSample_Contradiction_core h as (← getLCtx) (← getLocalInstances)
    match sub with
    | .none => IO.println "Not contradiction"
    | .some sub =>
        IO.println "Sub"
        for nex in sub do
          IO.println s!"Type: {← ppExpr (← inferType nex)}\nTerm: {← ppExpr ( nex)}"


#check 1

open List


theorem test_1 (n : Nat) (h1 : n = 42) (h2 : n ≠ 42) : n = 37 := by
  exfalso
  exact h2 h1

-- #eval test_exfalso_sample `test_1

-- #eval test_contra_sample `test_1

theorem test_2 (n : Nat) (h1 : n = 42) (h2 : n ≠ 42) : n = 37 := by
  contradiction

-- #eval test_exfalso_sample `test_2

-- #eval test_contra_sample `test_2

theorem test_3 (n : Nat) (h1 : n.succ = 0) : n = 37 := by
  contradiction

-- #eval test_contra_sample `test_3


theorem test_4 (l : List Nat) (h1 : [] = 37 :: l) : l = [37] := by
  contradiction

-- #eval test_contra_sample `test_4



theorem test_5 (l : List Nat) (h1 : [1,2,3].length = 7) : l = [37] := by
  contradiction

-- #print test_5

-- #eval test_contra_sample `test_5


theorem test_6 (l : List Nat) (h1 : l ≠ l) : l = [37] := by
  contradiction

-- #print test_6

-- #eval test_contra_sample `test_6


theorem test_7 (l : List Nat) : l = [37] := by
  by_contra h
  sorry


-- #print test_7

-- #eval test_exfalso_sample `test_7
