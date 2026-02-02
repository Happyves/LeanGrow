

import LeanGrow.Src.SampleGenScore.Sample

open Lean Meta


def test (thmName : Name) (depth : Nat) : MetaM Unit := do
  let .some (.thmInfo I) := (← getEnv).find? thmName | throwError "Bad name"
  lambdaTelescope I.value <| fun fvs p => do
    let preS ← mkPreProCongr
    let .mk res _ l1 l2 ← digExpr preS (← getLCtx) (← getLocalInstances) depth (.raw p) .nil (fvs.map Expr.fvarId!).toList
    withLCtx l1 l2 <| do
      res.foldlM () (fun subp fvs _ => do
        IO.println "\nSample:\nLifted:"
        fvs.foldlM (fun _ fv => do IO.println s!" {fv.name} : {← ppExpr (← fv.getType)}") ()
        IO.println "SubProof types:"
        let _ ← match subp with
          | .raw P => IO.println s!" · {← ppExpr (← inferType P)}"
          | _ => IO.println "todo"
        IO.println "SubProof terms:"
        match subp with
        | .raw P => IO.println s!" · {← ppExpr P}"
        | _ => IO.println "todo"
        )

#check 1


-- # Apply

axiom A (n m : Nat) : Prop

axiom a1 (h : A n m) : A (n+1) m

axiom a2 (h1 : A n m) (h2 : A m n) : A n (m+1)


theorem test_1 (h1 : A 3 4) (h2 : A 1 4) (h3 : A 3 1) (h4 :  A 2 3) (h5 : A 2 2) : A 4 4 := by
  apply a2
  · apply a2
    · apply a2
      · apply a1
        exact h3
      · exact h2
    · apply a2
      · exact h4
      · apply a1
        exact h5
  · exact h1


-- #eval test `test_1 1

-- #eval test `test_1 0

-- #eval test `test_1 2

-- #eval test `test_1 5



#check 1


-- # Have

theorem test_2 (h1 : A 3 4) (h2 : A 1 4) (h3 : A 3 1) (h4 :  A 2 3) (h5 : A 2 2) : A 4 4 := by
  have H : A 4 2 := by
    apply a2
    · apply a1
      exact h3
    · exact h2
  apply a2
  · apply a2
    · exact H
    · apply a2
      · exact h4
      · apply a1
        exact h5
  · exact h1


-- #eval test `test_2 1

-- #eval test `test_2 0

-- #eval test `test_2 2

-- #eval test `test_2 3


theorem test_2_1 (h4 :  A 2 3) : A 4 4 := by
  have H : A 3 3 := by
    apply a1
    exact h4
  apply a2
  · apply a1
    exact H
  · apply a2
    · exact H
    · exact H


-- #eval test `test_2_1 1

-- #eval test `test_2_1 0

-- #eval test `test_2_1 2

-- #eval test `test_2_1 3




-- # Revert

theorem test_3 (h1 : A 3 4) (h2 : A 1 4) (h3 : A 3 1) (h4 :  A 2 3) (h5 : A 2 2) : A 4 4 := by
  apply a2
  · apply a2
    revert h1
    intro h1
    · apply a2
      · apply a1
        exact h3
      · exact h2
    · revert h4 h1
      intro h1 h4
      apply a2
      · exact h4
      · apply a1
        exact h5
  · exact h1


-- #eval test `test_3 1

-- #eval test `test_3 0

-- #eval test `test_3 2

-- #eval test `test_3 3



theorem test_4_1 (n : Nat) (h1 : A n n) : A n (n+2) := by
  apply a2
  · apply a2 <;> exact h1
  · apply a1 h1

-- #eval test `test_4_1 1

-- #eval test `test_4_1 0

theorem test_4_2 (n : Nat) (h1 : A n n) : A n (n+2) := by
  apply a2
  · revert n
    intro n h1
    apply a2 <;> exact h1
  · revert n
    intro n h1
    apply a1 h1

-- #eval test `test_4_2 1

-- #eval test `test_4_2 0

-- #eval test `test_4_2 2

-- # Rewrite

axiom a3 : A 8 9 ↔ A 3 2

axiom a4 (h : A n n.succ): A (n+2) n ↔ A n (n+3)


theorem test_5 (h : ∀ n, A n n): A 8 11 := by
  rw [← a4]
  · apply a1
    apply a1
    apply h
  · rw [a3]
    apply a1
    apply h

-- #eval test `test_5 1

-- #eval test `test_5 0

-- #eval test `test_5 2



-- # Subst


theorem test_6 (e : n = m) (h1 : A n 3) (h2 : A 4 m) (h3 : A n n) : A (n+1) (m+1) := by
  subst e
  apply a1
  apply a2 <;> exact h3


-- #eval test `test_6 1

-- #eval test `test_6 0


theorem test_7 (e : n = m) (h1 : A n 3) (h2 : A 4 m) (h3 : A n n) : A (n+1) (m+1) := by
  apply a2
  · apply a1
    subst e
    exact h3
  · subst e
    apply a2 <;> exact h3


-- #eval test `test_7 1

-- #eval test `test_7 0

-- #eval test `test_7 2



-- # Intro

theorem test_8
  (h1 : (∀ n, A n 2) → ∀ n, A n (n+2))
  (h2 : (∀ n, A 1 n) → ∀ n, A n 2)
  (h3 : ∀ n, A 1 n)
  : A 2 4 := by
    apply h1
    intro n
    apply h2
    intro m
    apply h3



-- #eval test `test_8 1

-- #eval test `test_8 0

-- #eval test `test_8 2

-- #eval test `test_8 3


theorem test_9
  (h1 : (∀ n, A n 2) → (∀ n, A 2 n) → ∀ n, A n (n+2))
  (h2 : (∀ n, A 2 n) → ∀ n, A n 2)
  (h3 : ∀ n, A 1 n)
  : A 2 4 := by
    apply h1
    · intro n
      apply h2
      intro m
      apply a1
      apply h3
    · intro m
      apply a1
      apply h3


-- #eval test `test_9 1

-- #eval test `test_9 0

-- #eval test `test_9 2

-- #eval test `test_9 3
