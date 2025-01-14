
import LeanGrow.F.EnvironmentManagement.SampleRegular.Sample



open Lean Meta


elab "runTest" i:num n:name : command => do
  let .some thm := (← getEnv).find?  n.getName | pure ()
  let .some proof := thm.value? | pure ()
  let iter := i.getNat
  let res ← Elab.Command.liftTermElabM
    ((lambdaLetTelescope proof
      (fun _ head => do
        let res ← contextualize iter head
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

runTest 1 `test1
runTest 2 `test1
runTest 3 `test1
runTest 4 `test1
runTest 5 `test1




theorem test2 (n m p : Nat) (hb : n ∣ p + m) : n ∣ Nat.gcd (2*n + (m + p)) n := by
  rw [Nat.dvd_gcd_iff]
  apply And.intro
  · apply Nat.dvd_add
    · apply Nat.dvd_mul_left
    · rw [Nat.add_comm]
      exact hb
  · apply Nat.dvd_refl

#print test2

runTest 1 `test2
runTest 2 `test2
runTest 3 `test2
runTest 4 `test2
runTest 5 `test2
runTest 6 `test2
runTest 7 `test2
runTest 8 `test2



elab "runTest2" i:num n:name : command => do
  let .some thm := (← getEnv).find?  n.getName | pure ()
  let .some proof := thm.value? | pure ()
  let iter := i.getNat
  let res ← Elab.Command.liftTermElabM
    ((lambdaLetTelescope proof
      (fun _ head => do
        let res ← subproofs iter head
        let pp ← res.mapM (fun l => l.mapM ppExpr)
        let out := pp.map (fun x => ("Context:\n" : Format) ++ (Std.Format.join (x.map (fun y => y ++ ("\n" : Format)))))
        return out
        )
      (cleanupAnnotations := true)) : MetaM _)
  IO.println ((Std.Format.join (res.map (fun y => y ++ ("\n\n" : Format)))))

runTest2 1 `test1
runTest2 2 `test1
runTest2 3 `test1
runTest2 4 `test1
runTest2 5 `test1

runTest2 1 `test2
runTest2 2 `test2
runTest2 3 `test2
runTest2 4 `test2
runTest2 5 `test2
runTest2 6 `test2
runTest2 7 `test2
runTest2 8 `test2


elab "runTest3" i:num n:name : command => do
  let .some thm := (← getEnv).find?  n.getName | pure ()
  let .some proof := thm.value? | pure ()
  let iter := i.getNat
  let res ← Elab.Command.liftTermElabM
    ((lambdaLetTelescope proof
      (fun _ head => do
        let res ← sampleForwSteps iter head
        let mut all := []
        for ⟨k,n,g,c⟩ in res do
          let ppc ← c.mapM ppExpr
          let ppg ← ppExpr g
          let out := (s!"Context:\nGoal: {ppg}\nKind : {repr k}\nName : {n}\n" : Format) ++ (Std.Format.join (ppc.map (fun y => y ++ ("\n" : Format))))
          all := out :: all
        return all
        )
      (cleanupAnnotations := true)) : MetaM _)
  IO.println ((Std.Format.join (res.map (fun y => y ++ ("\n\n" : Format)))))



runTest3 1 `test1
runTest3 2 `test1
runTest3 3 `test1
runTest3 4 `test1
runTest3 5 `test1

runTest3 1 `test2
runTest3 2 `test2
runTest3 3 `test2
runTest3 4 `test2
runTest3 5 `test2
runTest3 6 `test2
runTest3 7 `test2
runTest3 8 `test2


elab "runTest4" i:num n:name : command => do
  let .some thm := (← getEnv).find?  n.getName | pure ()
  let .some proof := thm.value? | pure ()
  let iter := i.getNat
  let res ← Elab.Command.liftTermElabM
    ((lambdaLetTelescope proof
      (fun _ head => do
        let res ← sampleForw iter head
        let mut all := []
        for ⟨k,n,g,c⟩ in res do
          let ppc ← c.mapM ppExpr
          let ppg ← ppExpr g
          let out := (s!"Context:\nGoal: {ppg}\nKind : {repr k}\nName : {n}\n" : Format) ++ (Std.Format.join (ppc.map (fun y => y ++ ("\n" : Format))))
          all := out :: all
        return all
        )
      (cleanupAnnotations := true)) : MetaM _)
  IO.println ((Std.Format.join (res.map (fun y => y ++ ("\n\n" : Format)))))

runTest4 1 `test1
runTest4 2 `test1
runTest4 3 `test1
runTest4 4 `test1
runTest4 5 `test1

runTest4 1 `test2
runTest4 2 `test2
runTest4 3 `test2
runTest4 4 `test2
runTest4 5 `test2
runTest4 6 `test2
runTest4 7 `test2
runTest4 8 `test2

elab "runTest5" i:num n:name : command => do
  let .some thm := (← getEnv).find?  n.getName | pure ()
  let .some proof := thm.value? | pure ()
  let iter := i.getNat
  let res ← Elab.Command.liftTermElabM
    ((lambdaLetTelescope proof
      (fun _ head => do
        let res ← SampleForw iter head
        let mut all := []
        for ⟨k,n,g,c⟩ in res do
          let ppc := c.map repr
          let ppg := repr g
          let out := (s!"Context:\nGoal: {ppg}\nKind : {repr k}\nName : {n}\n" : Format) ++ (Std.Format.join (ppc.map (fun y => y ++ ("\n" : Format))))
          all := out :: all
        return all
        )
      (cleanupAnnotations := true)) : MetaM _)
  IO.println ((Std.Format.join (res.map (fun y => y ++ ("\n\n" : Format)))))


runTest5 1 `test1
runTest5 2 `test1

runTest5 1 `test2
runTest5 2 `test2
runTest5 3 `test2
runTest5 4 `test2
