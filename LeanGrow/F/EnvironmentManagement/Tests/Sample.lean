
import LeanGrow.F.EnvironmentManagement.SampleRegular.Sample



open Lean Meta


elab "runTest" n:name : command => do
  let .some thm := (← getEnv).find?  n.getName | pure ()
  let .some proof := thm.value? | pure ()
  let res ← Elab.Command.liftTermElabM
    ((lambdaLetTelescope proof
      (fun _ head => do
        let res ← contextualize 3 head
        let pp ← res.mapM (fun l => l.mapM ppExpr)
        let out := pp.map (fun x => ("Context:\n" : Format) ++ (Std.Format.join (x.map (fun y => y ++ ("\n" : Format)))))
        return out
        )
      (cleanupAnnotations := true)) : MetaM _)
  IO.println ((Std.Format.join (res.map (fun y => y ++ ("\n\n" : Format)))))


theorem test1 (n m p : Nat) (ha : n ∣ m) (hb : n ∣ p) : n ∣ p + m := by
  rw [Nat.add_comm]
  apply Nat.dvd_add
  exact ha
  exact hb

#print test1

runTest `test1



theorem test2 (n m p : Nat) (hb : n ∣ p + m) : n ∣ Nat.gcd (2*n + (m + p)) n := by
  rw [Nat.dvd_gcd_iff]
  apply And.intro
  · apply Nat.dvd_add
    · apply Nat.dvd_mul_left
    · rw [Nat.add_comm]
      exact hb
  · apply Nat.dvd_refl

#print test2
