
import LeanGrow.F.EnvironmentManagement.SampleRegular.ExtractApply

open Lean Meta

elab "runTest" n:name : command => do
  let .some thm := (← getEnv).find?  n.getName | pure ()
  let .some proof := thm.value? | pure ()
  let res ← Elab.Command.liftTermElabM (lambdaLetTelescope proof (fun _ head => extractApply_main head ) (cleanupAnnotations := true))
  IO.println (repr res)


theorem test1 (n : Nat) (h : ∀ m, m = 42) : n = 42 := by
  apply h

#print test1

theorem test2 (n m: Nat) : n + m = m + n := by
  apply Nat.add_comm

#print test2

theorem test3 (n m k : Nat) (h : k ≤ m) : n + m - k = n + (m - k) := by
  apply Nat.add_sub_assoc
  exact h

#print test3


runTest `test1
runTest `test2
runTest `test3
