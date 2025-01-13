

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

elab "runTestAll" n:name : command => do
  let .some thm := (← getEnv).find?  n.getName | pure ()
  let .some proof := thm.value? | pure ()
  let res ← Elab.Command.liftTermElabM (lambdaLetTelescope proof (fun _ head => extractRWall_main head ) (cleanupAnnotations := true))
  IO.println (repr res)


runTest `test1
runTestAll `test1

runTest `test2
runTestAll `test2

runTest `test3
runTestAll `test3



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
runTestAll `test4
runTest2 `test5
runTestAll `test5
runTest2 `test6
runTestAll `test6
runTest2 `test7
runTestAll `test7
runTest2 `test8
runTestAll `test8
runTest2 `test9
runTestAll `test9


theorem test10 (n m p : Nat) (hb : n ∣ 2 * n + (m + p)) : n ∣ Nat.gcd (2*n + (m + p)) n := by
  rw [Nat.dvd_gcd_iff]
  constructor
  · exact hb
  · apply Nat.dvd_refl


#print test10

theorem test11 (n m p : Nat) (hb : n ∣ Nat.gcd (2*n + (m + p)) n) : n ∣ 2 * n + (m + p) ∧ n ∣ n := by
  rw [← Nat.dvd_gcd_iff]
  assumption

#print test11


runTest `test10
runTestAll `test10
runTest `test11
runTestAll `test11
