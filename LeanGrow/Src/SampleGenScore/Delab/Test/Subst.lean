
import LeanGrow.Src.SampleGenScore.Delab.Subst

import Mathlib.Data.List.Dedup

set_option linter.style.longLine false

open Lean Meta



def test_subst_sample (n : Name) : MetaM Unit := do
  let .some info := (← getEnv).find? n | throwError "Bad name"
  lambdaTelescope info.value! <| fun _ b => do
    let h := b.getAppFn'
    let as := b.getAppArgs
    let .mk sub l1 l2 ← delabSample_subst_core h as (← getLCtx) (← getLocalInstances)
    match sub with
    | .none => IO.println "Not subst"
    | .some sub =>
      withLCtx l1 l2 <| do
        IO.println "Sub"
        for nex in sub do
          IO.println s!"Type: {← ppExpr (← inferType nex)}\nTerm: {← ppExpr ( nex)}"


#check 1

open List

variable {α : Type*} [DecidableEq α]


theorem test_1 {a : α} {l L : List α}
  (h : a ∈ dedup l) (H : l.dedup = L) : dedup (a :: l) = L := by
    subst H
    rw [dedup_cons_of_mem']
    exact h

-- #print test_1

-- #eval test_subst_sample `test_1


theorem test_2 {a b : α} {l : List α}
  (h : b ∈ dedup l) (H : b = a) : dedup (a :: l) =  dedup l := by
  subst H
  rw [dedup_cons_of_mem']
  exact h

-- #print test_2

-- #eval test_subst_sample `test_2


theorem test_3 {a b : α} {l : List α}
  (h : b ∈ dedup l) (H : a = b) : dedup (a :: l) =  dedup l := by
  subst H
  rw [dedup_cons_of_mem']
  exact h

-- #print test_3

-- #eval test_subst_sample `test_3
