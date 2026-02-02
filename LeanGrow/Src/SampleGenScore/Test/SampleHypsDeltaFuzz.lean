
import LeanGrow.Src.SampleGenScore.Sample

open Lean Meta


def test (thmName : Name) (depthStart depthStop deltaFuel zetaFuel: Nat) : MetaM Unit := do
  let .some (.thmInfo I) := (← getEnv).find? thmName | throwError "Bad name"
  lambdaTelescope I.value <| fun fvs p => do
    let preS ← mkPreProCongr
    let .mk res l1 l2 ← sampleHypsCore preS (← getLCtx) (← getLocalInstances) depthStart depthStop p (fvs.map Expr.fvarId!).toList (.some deltaFuel) (.some zetaFuel)
    withLCtx l1 l2 <| do
      res.foldlM () (fun fvs subps _ => do
        IO.println "\nSample:\nLifted:"
        fvs.foldlM (fun _ fv => do IO.println s!" {fv.name} : {← ppExpr (← fv.getType)}") ()
        IO.println "SubProof types:"
        subps.foldlM (fun _ subp => do
          match subp with
          | .raw P => IO.println s!" · {← ppExpr (← inferType P)}"
          | _ => IO.println "todo"
          ) ()
        IO.println "SubProof terms:"
        subps.foldlM (fun _ subp => do
          match subp with
          | .raw P => IO.println s!" · {← ppExpr P}"
          | _ => IO.println "todo"
          ) ()
        )

#check 1


axiom A (n m : Nat) : Prop

axiom a1 {n m} (h : A n m) : A (n+1) m

axiom a2 {n m} (h1 : A n m) (h2 : A m n) : A n (m+1)

theorem d1 {n m} (h : A n m) : A (n+3) m := by
  apply a1
  apply a1
  apply a1
  exact h

axiom a3 {n m} (h : A n (m+2)) : n = m

theorem d2 {n m} (h1 : A n (m+1)) (h2 : A (m+1) n) : n = m := by
  apply a3
  exact a2 h1 h2


-- # Test


theorem test_1 (h : A 8 8) : A 11 8 := by
  apply d1
  exact h

-- #eval test `test_1 0 3 1 1

-- #eval test `test_1 1 3 1 1

-- #eval test `test_1 2 3 1 1

-- #eval test `test_1 0 2 1 1

-- #eval test `test_1 1 2 1 1




theorem test_2 {n m} (h1 : A n (m+1)) (h2 : A m n) (h3 : A m m) : A n m := by
  rw [@d2 n m]
  · exact h3
  · exact h1
  · apply a1
    exact h2



-- #eval test `test_2 0 3 1 1

-- #eval test `test_2 1 3 1 1

-- #eval test `test_2 2 3 1 1

-- #eval test `test_2 0 2 1 1

-- #eval test `test_2 1 2 1 1


theorem test_3 (h4 :  A 2 3) : A 4 4 := by
  have H : A 3 3 := by
    apply a1
    exact h4
  apply a2
  · apply a1
    exact H
  · apply a2
    · exact H
    · exact H


-- tracing_mode .std
-- tracing_flags [(`sampleHypsCore.inner, TracingFlags.all), (`sampleHypsCore.go, TracingFlags.all),]

-- #eval test `test_3 0 3 1 1

-- #eval test `test_3 1 3 1 1

-- #eval test `test_3 0 4 1 1

-- #eval test `test_3 1 4 1 1
