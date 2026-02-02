
import LeanGrow.Src.SampleGenScore.Delab.CongrConvert

import Mathlib.Algebra.BigOperators.Pi

set_option linter.style.longLine false

open Lean Meta


partial def test_con_sample_core (v : Expr) : MetaM Unit := do
  lambdaTelescope v <| fun _ b => do
    match b.getAppFn' with
    | .const n _ =>
      match n with
      | ``eq_of_heq | ``heq_of_eq | ``pi_congr =>
        IO.println s!"Skpping {n}"
        test_con_sample_core (b.getArg! 3)
      | ``funext  =>
        IO.println s!"Skpping {n}"
        test_con_sample_core (b.getArg! 4)
      | ``propext | ``iff_of_eq =>
        IO.println s!"Skpping {n}"
        test_con_sample_core (b.getArg! 2)
      | _ =>
        let .mk lif sub l1 l2 ← delabSample_CongrConvert_core b (← getLCtx) (← getLocalInstances)
        withLCtx l1 l2 <| do
          match sub with
          | .none => IO.println "Not congr or convert"
          | .some sub =>
              IO.println "Lifted"
              for l in lif do
                IO.println s!"Type: {← ppExpr (← l.getType)}\nTerm (?): {← (do match ← l.getDecl with | .ldecl _ _ _ _ V .. => ppExpr V | _ => return "none")}"
              IO.println "Unlifted"
              for nex in sub do
                IO.println s!"Type: {← ppExpr (← inferType nex)}\nTerm: {← ppExpr ( nex)}"
    | _ =>
      let .mk lif sub l1 l2 ← delabSample_CongrConvert_core b (← getLCtx) (← getLocalInstances)
      withLCtx l1 l2 <| do
        match sub with
        | .none => IO.println "Not congr or convert"
        | .some sub =>
            IO.println "Lifted"
            for l in lif do
              IO.println s!"Type: {← ppExpr (← l.getType)}\nTerm (?): {← (do match ← l.getDecl with | .ldecl _ _ _ _ V .. => ppExpr V | _ => return "none")}"
            IO.println "Unlifted"
            for nex in sub do
              IO.println s!"Type: {← ppExpr (← inferType nex)}\nTerm: {← ppExpr ( nex)}"


def test_con_sample (n : Name) : MetaM Unit := do
  let .some info := (← getEnv).find? n | throwError "Bad name"
  test_con_sample_core info.value!



theorem test_1 (n m k : Nat) : n + m - k = k + m - n := by
  congr
  all_goals sorry


#print test_1
#eval test_con_sample `test_1

def testh (n : Nat) (x : Fin n) : Nat := sorry


theorem test_2 (n m : Nat) (x : Fin n) (y : Fin m) : testh n x = testh m y := by
  congr
  all_goals sorry


#print test_2
#eval test_con_sample `test_2


theorem test_3 (n m : Nat) (x : Fin n) (y : Fin m) : testh n x = testh m y := by
  congr!
  all_goals sorry

#print test_3
#eval test_con_sample `test_3


theorem test_4 (n m : Nat) (x : Fin n) (y : Fin m) : (∀ k, testh n x = k) = (∀ k, testh m y = k) := by
  congr!
  all_goals sorry

#print test_4
#eval test_con_sample `test_4
