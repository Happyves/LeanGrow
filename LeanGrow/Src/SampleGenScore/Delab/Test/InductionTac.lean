

import LeanGrow.Src.SampleGenScore.Delab.ObtainRcasesBycases
import LeanGrow.Src.Utils.Lean.Expr.Basic


import Mathlib.Data.Nat.GCD.Basic


open Lean Meta


def test_main_sample (n : Name) : MetaM Unit := do
  let .some info := (← getEnv).find? n | throwError "Bad name"
  lambdaTelescope info.value! <| fun _ b => do
    let b := b.zeta
    let .mk sub l1 l2 ← delabSample_ObtRCaseIndCase_core b (← getLCtx) (← getLocalInstances)
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
    let b := b.zeta
    let .mk sub l1 l2 ← delabDig_ObtRCaseIndCase_core b (← getLCtx) (← getLocalInstances)
    match sub with
    | .none => IO.println "Not induction"
    | .some sub =>
        withLCtx l1 l2 <| do
          IO.println "Sub"
          for nex in sub do
            IO.println s!"Type: {← ppExpr (← inferType nex)}\nTerm: {← ppExpr ( nex)}"


def test_main_topB (n : Name) : MetaM Unit := do
  let .some info := (← getEnv).find? n | throwError "Bad name"
  lambdaTelescope info.value! <| fun _ b => do
    let b := b.zeta
    let sub ← delabSample_ObtRCaseIndCase_topBack b
    IO.println s!"Sample: {←  sub.pp}"

def test_main_topF (n : Name) : MetaM Unit := do
  let .some info := (← getEnv).find? n | throwError "Bad name"
  lambdaTelescope info.value! <| fun _ b => do
    let b := b.zeta
    let sub ← delabSample_ObtRCaseIndCase_topForw b
    IO.println s!"Recognized: {sub}"


#check Eq.refl


theorem test_1 (l : List Nat) : 42 = 42 := by
  cases l with
  | nil => rfl
  | cons _ _ => rfl

-- #print test_1

-- #eval test_main_sample `test_1
-- #eval test_main_dig `test_1
-- #eval test_main_topB `test_1
-- #eval test_main_topF `test_1


theorem test_2 (l : List Nat) (h : l.Nodup) : 42 = 42 := by
  cases l with
  | nil => rfl
  | cons _ _ => rfl

-- #print test_2

-- #eval test_main_sample `test_2
-- set_option pp.funBinderTypes true
-- #eval test_main_dig `test_2
-- #eval test_main_topB `test_2
-- #eval test_main_topF `test_2



theorem test_3 (l : List Nat)
  (h1 : l.Nodup) (h2 : 42 ∉ l)
  : let h3 : (42 :: l).Nodup := (by rw [List.nodup_cons] ; exact ⟨h2,h1⟩) ; (42 :: l).Nodup:= by
  cases l with
  | nil => intro x ; exact x
  | cons _ _ =>  intro x ; exact x

-- #print test_3

-- #eval test_main_sample `test_3
-- #eval test_main_dig `test_3
-- #eval test_main_topB `test_3
-- #eval test_main_topF `test_3


theorem test_4 (l : List Nat) (h : l.Nodup) : 42 = 42 := by
  induction l with
  | nil => rfl
  | cons _ _ _ => rfl

-- #print test_4

-- #eval test_main_sample `test_4
-- #eval test_main_dig `test_4
-- #eval test_main_topB `test_4
-- #eval test_main_topF `test_4


#check List.map.induct

theorem test_5 (l : List Nat) (h : l.Nodup) : 42 = 42 := by
  induction l using List.map.induct with
  | case1 => rfl
  | case2 _ _ _ => rfl


-- #eval test_main_sample `test_5
-- #eval test_main_dig `test_5
-- #eval test_main_topB `test_5
-- #eval test_main_topF `test_5


theorem test_6 (p : Nat × Nat) : 42 = 42 := by
  obtain ⟨a,b⟩ := p
  rfl

-- #eval test_main_sample `test_6
-- #eval test_main_dig `test_6
-- #eval test_main_topB `test_6
-- #eval test_main_topF `test_6

theorem test_7 : ∀ _ : Nat × Nat, 42 = 42 := by
  rintro ⟨a,b⟩
  rfl

-- #eval test_main_sample `test_7
-- #eval test_main_dig `test_7
-- #eval test_main_topB `test_7
-- #eval test_main_topF `test_7



theorem test_8 (p : (Nat × Nat) ⊕ Int) : 42 = 42 := by
  rcases p with (⟨a,b⟩ | c)
  · rfl
  · rfl


-- #eval test_main_sample `test_8
-- #eval test_main_dig `test_8
-- #eval test_main_topB `test_8
-- #eval test_main_topF `test_8


theorem test_9 : 42 = 42 := by
  by_cases q : 2 = 2
  · rfl
  · rfl

-- #eval test_main_sample `test_9
-- #eval test_main_dig `test_9
-- #eval test_main_topB `test_9
-- #eval test_main_topF `test_9


theorem test_10 (l : List Nat) (h : l = 37 :: l) : False := by
  cases h

-- #print test_10

-- #eval test_main_sample `test_10
-- #eval test_main_dig `test_10
-- #eval test_main_topB `test_10
-- #eval test_main_topF `test_10

example (l : List Nat) (h : l = 37 :: l) : False := by
  revert h
  generalize 37 = n
  induction l with
  | nil => intro no ; contradiction
  | cons x xs ih =>
    intro h
    obtain ⟨h1,h2⟩ := List.cons.inj h
    apply ih
    rwa [← h1]

open Nat

theorem test_11 {m n a b : ℕ} (cop : Coprime m n) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a * m + b * n = m * n) : False := by
  obtain ⟨x, rfl⟩ : n ∣ a :=
    cop.symm.dvd_of_dvd_mul_right
      ((Nat.dvd_add_iff_left (Nat.dvd_mul_left n b)).mpr
        ((congr_arg _ h).mpr (Nat.dvd_mul_left n m)))
  sorry

#print test_11


#eval test_main_sample `test_11
#eval test_main_dig `test_11
#eval test_main_topB `test_11
#eval test_main_topF `test_11


#check Exists.casesOn
