

import LeanGrow.F.EnvironmentManagement.SampleRegular.ExtractRW

open Lean Meta



theorem test1 (n m : Nat) (hnm : n = m) (hn : n = 42) : m = 42 := by
  rw [← hnm]
  exact hn

theorem test2 (n m p: Nat) : (n + m) + p = p + (n + m) := by
  rw [Nat.add_comm]

#print test2

#check Nat.sub_add_comm

theorem test3 (n m p: Nat) (h : p ≤ n) : n + (n + m - p) = n + (n - p + m) := by
  rw [Nat.sub_add_comm]
  assumption

elab "runTest" n:name : command => do
  let .some thm := (← getEnv).find?  n.getName | pure ()
  let .some proof := thm.value? | pure ()
  let res ← Elab.Command.liftTermElabM (lambdaLetTelescope proof (fun _ head => extractRW_main head ) (cleanupAnnotations := true))
  IO.println (repr res)

runTest `test1

runTest `test2

runTest `test3

/-

convert requires import Mathlib.Tactic which clashes with my stuff, for some reason

theorem test3 (n m p k: Nat) (hnm : n = m) (hpk : p = k) (hn : n + p = 42)
  : m + k = 42 := by
  convert hn
  exact hnm.symm
  exact hpk.symm

#print test3

theorem test4 (n m p k: Nat) (hnm : n = m) (hpk : p = k) (hn : n  = p)
  : m = k := by
  convert hn
  exact hnm.symm
  exact hpk.symm

#print test4


theorem test5 (n m p k r s: Nat) (hnm : n = m) (hpk : p = k) (hrs : r = s) (hn : n +p +r  = 42)
  : m + k + s = 42 := by
  convert hn
  exact hnm.symm
  exact hpk.symm
  exact hrs.symm


#print test5

-/


theorem test4 (n m : Nat) (hnm : n = m) (f : Nat → Nat) : f n = f m := by
  congr

#print test4

theorem test5 (n m : Nat → Nat) (hnm : n = m) (f : Nat) : n f = m f :=
  -- by congr -- does nothing lol
  @Eq.ndrec _ _ (fun x : Nat → Nat => n f = x f)  rfl _ hnm

theorem test6 (n m : Nat → Nat) (hnm : n = m) (f : Nat) : n f = m f :=
  -- by congr -- does nothing lol
  @Eq.rec _ _ (fun x _ => n f = x f)  rfl _ hnm

theorem test7 (n m : Nat → Nat) (hnm : n = m) (f : Nat) : n f = m f :=
  -- by congr -- does nothing lol
  @Eq.recOn _ _ (fun x _ => n f = x f) _ hnm rfl

theorem test8 (n m : Nat → Nat) (hnm : n = m) (f : Nat) : n f = m f :=
  -- by congr -- does nothing lol
  @Eq.casesOn _ _ (fun x _ => n f = x f) _ hnm rfl

theorem test9 (n m : Nat) (f : Nat → Nat) : f (n+m) = f (m+n) :=
  -- by congr -- does nothing lol
  @Eq.casesOn _ _ (fun x _ => f (n+m) = f x) _ (Nat.add_comm n m) rfl



elab "runTest2" n:name : command => do
  let .some thm := (← getEnv).find?  n.getName | pure ()
  let .some proof := thm.value? | pure ()
  let res ← Elab.Command.liftTermElabM (lambdaLetTelescope proof (fun _ head => extractCongrRaw_main head ) (cleanupAnnotations := true))
  IO.println (repr res)

runTest2 `test4
runTest2 `test5
runTest2 `test6
runTest2 `test7
runTest2 `test8
runTest2 `test9
