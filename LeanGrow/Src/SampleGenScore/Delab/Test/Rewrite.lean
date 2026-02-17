

import LeanGrow.Src.SampleGenScore.Delab.Rewrite

import Mathlib.Data.List.Dedup

set_option linter.style.longLine false

open Lean Meta


def test_rewrite_sample (n : Name) : MetaM Unit := do
  let .some info := (← getEnv).find? n | throwError "Bad name"
  lambdaTelescope info.value! <| fun _ b => do
    let h := b.getAppFn'
    let as := b.getAppArgs
    let .mk lif sub delzet l1 l2 ← delabSample_Rewrite_core h as (← getLCtx) (← getLocalInstances)
    match sub with
    | .none => IO.println "Not an rw"
    | .some sub =>
      withLCtx l1 l2 <| do
        IO.println "Lifted"
        for l in lif do
          IO.println s!"Type: {← ppExpr (← l.getType)}\nTerm (?): {← (do match ← l.getDecl with | .ldecl _ _ _ _ V .. => ppExpr V | _ => return "none")}"
        IO.println "Sub"
        for nex in sub do
          IO.println s!"Type: {← ppExpr (← inferType nex)}\nTerm: {← ppExpr ( nex)}"
        match delzet with
        | .none => IO.println "No delzet"
        | .some delzet => IO.println s!"Delzet {← ppExpr delzet}"


def test_rewrite_dig (n : Name) : MetaM Unit := do
  let .some info := (← getEnv).find? n | throwError "Bad name"
  lambdaTelescope info.value! <| fun _ b => do
    let h := b.getAppFn'
    let as := b.getAppArgs
    let sub ← delabDig_Rewrite_core h as (← getLCtx) (← getLocalInstances)
    match sub with
    | .none => IO.println "Not an rw"
    | .some sub =>
      IO.println "Sub"
      for nex in sub do
        IO.println s!"Type: {← ppExpr (← inferType nex)}\nTerm: {← ppExpr ( nex)}"


def test_rewrite_topB (n : Name) : MetaM Unit := do
  let .some info := (← getEnv).find? n | throwError "Bad name"
  lambdaTelescope info.value! <| fun _ b => do
    let h := b.getAppFn'
    let as := b.getAppArgs
    let sub ← delabSample_Rewrite_topBack .empty h as (← getLCtx) (← getLocalInstances)
    IO.println s!"Sample: {← sub.mapM SampleData.pp}"


def test_rewrite_topF (n : Name) : MetaM Unit := do
  let .some info := (← getEnv).find? n | throwError "Bad name"
  lambdaTelescope info.value! <| fun _ b => do
    let h := b.getAppFn'
    let as := b.getAppArgs
    let sub ← delabSample_Rewrite_topForw h as (← getLCtx) (← getLocalInstances)
    match sub with
    | .none => IO.println "not an rw"
    | .some .none => IO.println "unsamplable rw"
    | .some (.some thm ini) => IO.println s!"Sample for {thm} with ini: {← ppExpr ini}"



#check 1

open List

theorem test_1 : [1,2].dedup.dedup = [1,2] := by
  rw [dedup_idem]
  decide


-- #eval test_rewrite_sample `test_1
-- #eval test_rewrite_dig `test_1
-- #eval test_rewrite_topB `test_1
-- #eval test_rewrite_topF `test_1

variable {α : Type*} [DecidableEq α]

theorem test_2 {a : α} {l L : List α}
  (h : a ∈ dedup l) (H : l.dedup = L) : dedup (a :: l) = L := by
    rw [dedup_cons_of_mem']
    · exact H
    · exact h

-- #eval test_rewrite_sample `test_2
-- #eval test_rewrite_dig `test_2
-- #eval test_rewrite_topB `test_2
-- #eval test_rewrite_topF `test_2


theorem test_3 {a b: α} {l L : List α} (hab : a = b)
  (h : b ∈ dedup l) (H : l.dedup = L) : dedup (a :: l) = L := by
    rw [dedup_cons_of_mem']
    · exact H
    · rw [hab]
      exact h

-- #eval test_rewrite_sample `test_3
-- #eval test_rewrite_dig `test_3
-- #eval test_rewrite_topB `test_3
-- #eval test_rewrite_topF `test_3


theorem test_4 {a b : α} {l L : List α} (hab : a = b)
  (h : b ∈ dedup l) (H : l.dedup = L) (r : (h : a ∈ l.dedup) → (a :: l).dedup = l.dedup)
  : dedup (a :: l) = L := by
    rw [r]
    · exact H
    · rw [hab]
      exact h

-- #eval test_rewrite_sample `test_4
-- #eval test_rewrite_dig `test_4
-- #eval test_rewrite_topB `test_4
-- #eval test_rewrite_topF `test_4
