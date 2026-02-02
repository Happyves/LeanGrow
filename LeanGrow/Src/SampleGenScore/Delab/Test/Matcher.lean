

import LeanGrow.Src.SampleGenScore.Delab.Matcher
import LeanGrow.Src.Utils.Lean.Expr.Basic

open Lean Meta


def test_main_sample (n : Name) : MetaM Unit := do
  let .some info := (← getEnv).find? n | throwError "Bad name"
  lambdaTelescope info.value! <| fun _ b => do
    let h := b.getAppFn'
    let as := b.getAppArgs
    let .mk sub l1 l2 ← delabSample_Matcher_core h as (← getLCtx) (← getLocalInstances)
    match sub with
    | .none => IO.println "Not induction"
    | .some sub =>
        withLCtx l1 l2 <| do
          IO.println "Sub"
          for nex in sub do
            IO.println s!"Type: {← ppExpr (← inferType nex)}\nTerm: {← ppExpr ( nex)}"


def test_main_dig (n : Name) : MetaM Unit := do
  let .some info := (← getEnv).find? n | throwError "Bad name"
  lambdaTelescope info.value! <| fun _ b => do
    let h := b.getAppFn'
    let as := b.getAppArgs
    let .mk sub l1 l2 ← delabDig_Matcher_core h as (← getLCtx) (← getLocalInstances)
    match sub with
    | .none => IO.println "Not induction"
    | .some sub =>
        withLCtx l1 l2 <| do
          IO.println "Sub"
          for nex in sub do
            IO.println s!"Type: {← ppExpr (← inferType nex)}\nTerm: {← ppExpr ( nex)}"


def test_main_top (n : Name) : MetaM Unit := do
  let .some info := (← getEnv).find? n | throwError "Bad name"
  lambdaTelescope info.value! <| fun _ b => do
    let h := b.getAppFn'
    let .mk sub _ _ ← delabSample_Matcher_top h (← getLCtx) (← getLocalInstances)
    IO.println s!"Recognized: {sub}"



theorem test_1 (x : Nat) : 42 = 42 := by
  match x with
  | 0 => rfl
  | n+1 => rfl

-- #eval test_main_sample `test_1
-- #eval test_main_dig `test_1
-- #eval test_main_top `test_1


theorem test_2 (x : Nat) : 42 = 42 := by
  match x with
  | 0 => rfl
  | 1
  | n+2 => rfl

-- #eval test_main_sample `test_2
-- #eval test_main_dig `test_2
-- #eval test_main_top `test_2



theorem test_3 (x : List Nat) : 42 = 42 := by
  match x with
  | [] => rfl
  | 42 :: l => rfl
  | 37 :: 42 :: l => rfl
  | _ :: _ => rfl


-- #eval test_main_sample `test_3
-- #eval test_main_dig `test_3
-- #eval test_main_top `test_3


theorem test_4 (x y : Nat) : 42 = 42 := by
  match x, y with
  | 0, 0 => rfl
  | n+1, m+1 => rfl
  | _, _ => rfl


-- #eval test_main_sample `test_4
-- #eval test_main_dig `test_4
-- #eval test_main_top `test_4


theorem test_5 (x : Nat) (h : x = 37) : 42 = 42 := by
  match x with
  | 0 => rfl
  | n+1 => rfl


-- #eval test_main_sample `test_5
-- #eval test_main_dig `test_5
-- #eval test_main_top `test_5



theorem test_6 (x : Nat) (h : x = 37) : 42 = 42 := by
  match D : x with
  | 0 => contradiction
  | n+1 => rfl


-- #eval test_main_sample `test_6
-- #eval test_main_dig `test_6
-- #eval test_main_top `test_6



inductive FinListSized (n : Nat) : Nat → Type where
| nil : FinListSized n 0
| cons (x : Fin n) (_ : FinListSized n i) : FinListSized n (i+1)

theorem test_7 (n : Nat) (x : FinListSized n n) (h1 : n = 37) (h2 : HEq x (@FinListSized.nil )) : 42 = 42 := by
  match D : x with
  | .nil => rfl
  | .cons _ _ => rfl


-- #eval test_main_sample `test_7
-- #eval test_main_dig `test_7
-- #eval test_main_top `test_7
