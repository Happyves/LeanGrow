
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
