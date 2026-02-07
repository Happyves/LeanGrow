

import LeanGrow.Src.SampleGenScore.Delab.Basic

import Mathlib.Data.List.Dedup

set_option linter.style.longLine false

open Lean Meta


def test_apply_sample (n : Name) : MetaM Unit := do
  let .some info := (← getEnv).find? n | throwError "Bad name"
  lambdaTelescope info.value! <| fun _ b => do
    let h := b.getAppFn'
    let as := b.getAppArgs
    let .mk _ res delZet _ _ ← delabSample_Apply_core h as (← getLCtx) (← getLocalInstances)
    let _ ← do
      match delZet with
      | .none => IO.println "Args:"
      | .some R => IO.println s!"delZet:\n{← ppExpr R}\nArgs:"
    let res := res.getD []
    for r in res do
      IO.println s!"· {← ppExpr r}"


def test_apply_dig (n : Name) : MetaM Unit := do
  let .some info := (← getEnv).find? n | throwError "Bad name"
  lambdaTelescope info.value! <| fun _ b => do
    let h := b.getAppFn'
    let as := b.getAppArgs
    let res ← delabDig_Apply_core h as (← getLCtx) (← getLocalInstances)
    let res := res.getD []
    IO.println "Args:"
    for r in res do
      IO.println s!"· {← ppExpr r}"


def test_apply_top (n : Name) : MetaM Unit := do
  let .some info := (← getEnv).find? n | throwError "Bad name"
  lambdaTelescope info.value! <| fun _ b => do
    let h := b.getAppFn'
    let as := b.getAppArgs
    let res ← delabSample_Apply_topBack .empty h as (← getLCtx) (← getLocalInstances)
    IO.println s!"{repr res}"


def test_havelet_sample (n : Name) : MetaM Unit := do
  let .some info := (← getEnv).find? n | throwError "Bad name"
  lambdaTelescope info.value! <| fun _ b => do
    match b with
    | .letE bi T V B _ =>
      let .mk lif nex l1 l2 ← delabSample_HaveLet_core bi T V B (← getLCtx) (← getLocalInstances)
      withLCtx l1 l2 <| do
        match lif with
        | .none =>
          IO.println s!"No lift, next: \nType: {← ppExpr (← inferType nex)}\nTerm: {← ppExpr ( nex)}"
        | .some lif =>
          IO.println s!"Lifted: \nType: {← ppExpr (← lif.getType)}\nTerm (?): {← (do match ← lif.getDecl with | .ldecl _ _ _ _ V .. => ppExpr V | _ => return "none")}"
          IO.println s!"Next: \nType: {← ppExpr (← inferType nex)}\nTerm: {← ppExpr ( nex)}"
    | _ =>
      IO.println "Not a let"


def test_revert_sample (n : Name) : MetaM Unit := do
  let .some info := (← getEnv).find? n | throwError "Bad name"
  lambdaLetTelescope info.value! <| fun _ b => do
    let h := b.getAppFn'
    let as := b.getAppArgs
    let .mk lif sub delzet l1 l2 ← delabSample_AssertDefineRevert_core h as (← getLCtx) (← getLocalInstances)
    withLCtx l1 l2 <| do
      IO.println "Lifted"
      for l in lif do
        IO.println s!"Type: {← ppExpr (← l.getType)}\nTerm (?): {← (do match ← l.getDecl with | .ldecl _ _ _ _ V .. => ppExpr V | _ => return "none")}"
      IO.println "Unlifted"
      for nex in sub do
        IO.println s!"Type: {← ppExpr (← inferType nex)}\nTerm: {← ppExpr ( nex)}"
      match delzet with
      | .none => IO.println "No delzet"
      | .some delzet => IO.println s!"Delzet {← ppExpr delzet}"


def test_revert_dig (n : Name) : MetaM Unit := do
  let .some info := (← getEnv).find? n | throwError "Bad name"
  lambdaLetTelescope info.value! <| fun _ b => do
    let h := b.getAppFn'
    let as := b.getAppArgs
    let .mk lif sub haveLike l1 l2 ← delabDig_AssertDefineRevert_core h as (← getLCtx) (← getLocalInstances)
    withLCtx l1 l2 <| do
      IO.println "Lifted"
      for l in lif do
        IO.println s!"Type: {← ppExpr (← l.getType)}\nTerm (?): {← (do match ← l.getDecl with | .ldecl _ _ _ _ V .. => ppExpr V | _ => return "none")}"
      IO.println "Unlifted"
      for nex in sub do
        IO.println s!"Type: {← ppExpr (← inferType nex)}\nTerm: {← ppExpr ( nex)}"
      IO.println "Have-like"
      for nex in haveLike do
        IO.println s!"Type: {← ppExpr (← inferType nex)}\nTerm: {← ppExpr ( nex)}"

def test_revert_top (n : Name) : MetaM Unit := do
  let .some info := (← getEnv).find? n | throwError "Bad name"
  lambdaLetTelescope info.value! <| fun _ b => do
    let h := b.getAppFn'
    let as := b.getAppArgs
    let dat ← delabSample_AssertDefineRevert_topBack .empty h as (← getLCtx) (← getLocalInstances)
    IO.println <| repr dat





open List

-- # Apply

theorem test_1 : [1,2,3].dedup <+ [1,2,3] := by
  apply dedup_sublist


-- #eval test_apply_sample `test_1
-- #eval test_apply_dig `test_1
-- #eval test_apply_top `test_1


theorem test_2 (h : Pairwise LT.lt [1,2,3]) : Nodup [1,2,3] := by
  apply @Pairwise.nodup _ _ _ ⟨Nat.lt_irrefl⟩
  exact h

-- #eval test_apply_sample `test_2
-- #eval test_apply_dig `test_2
-- #eval test_apply_top `test_2

theorem test_3 (h : Pairwise LT.lt [1,2,3]) : Nodup [1,2,3] := by
  apply @Pairwise.nodup _ _ _ ⟨Nat.lt_irrefl⟩
  decide

-- #eval test_apply_sample `test_3
-- #eval test_apply_dig `test_3
-- #eval test_apply_top `test_3


theorem test_4 : Nodup [1,2,3] := by
  decide

-- #eval test_apply_sample `test_4
-- #eval test_apply_dig `test_4
-- #eval test_apply_top `test_4


-- # Have-let

theorem test_1_1 : 42 = 42 := by
  have : 37 = 37 := rfl
  rfl

-- #print test_1_1

-- #eval test_havelet_sample `test_1_1


theorem test_1_2 (h : 37 = 37 → 42 = 42) : 42 = 42 := by
  have : 37 = 37 := rfl
  exact h this


-- #print test_1_2

-- #eval test_havelet_sample `test_1_2

theorem test_1_3 (h1 : ∀ n : Nat, 37 = 37 → n = n) (h2 : 2 = 2 → 3 = 3 → 42 = 666) : 42 = 666 := by
  have : 37 = 37 := rfl
  exact h2 (h1 2 this) (h1 3 this)


-- #print test_1_3

-- #eval test_havelet_sample `test_1_3


theorem test_1_4 : 42 = 42 := by
  let n := 37
  rfl

-- #print test_1_4

-- #eval test_havelet_sample `test_1_4


theorem test_1_5 (h1 : ∀ n : Nat, 37 = 37 → n = n) (h2 : 2 = 2 → 3 = 3 → 42 = 666) : 42 = 666 := by
  let F (x : Nat) := h1 x (Eq.refl 37)
  exact h2 (F 2) (F 3)

-- #print test_1_5

-- #eval test_havelet_sample `test_1_5

theorem test_1_6 (h1 : ∀ n : Nat, 37 = 37 → n = n) (h2 : 2 = 2 → 3 = 3 → 42 = 666) : 42 = 666 := by
  let F (x : Nat) := x+1
  have : 37 = 37 := rfl
  exact h2 (h1 (F 1) this) (h1 (F 2) this)

-- #print test_1_6

-- #eval test_havelet_sample `test_1_6



-- # Assert define revert



theorem test_2_1 (n : Nat) (h : n = 67) : 42 = 42 := by
  revert n
  intro _ _
  rfl


-- #eval test_revert_sample `test_2_1
-- #eval test_revert_dig `test_2_1
-- #eval test_revert_top `test_2_1


theorem test_2_2 (n : Nat) (h : n = 67) : let H : n + 3 = 70 := (by rw [h]) ; 42 = 42 := by
  intro
  revert n
  intro _ _ _
  rfl

-- #eval test_revert_sample `test_2_2
-- #eval test_revert_dig `test_2_2
-- #eval test_revert_top `test_2_2

theorem test_2_3 (n : Nat) (h : n = 67) (spe : 2 = 2 → 3 = 3 → 42 = 42) : let H : n + 3 = 70 := (by rw [h]) ; 42 = 42 := by
  intro
  revert n
  intro n h H
  have dummy (m : Nat) : n + 3 = 70 → m = m := by
    intro _ ; rfl
  apply spe
  · apply dummy _ H
  · apply dummy _ H

-- #eval test_revert_sample `test_2_3
-- #eval test_revert_dig `test_2_3
-- #eval test_revert_top `test_2_3
