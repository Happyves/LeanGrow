

import LeanGrow.Src.SampleGenScore.Gen.TestTools_SampleSubpat
import LeanGrow.Src.SampleGenScore.Gen.Tests.Test_Gen

open Lean Meta


def testSub_T (onlyInd : Bool) (thmNames : Array Name) :=
  test_subSample_cvbThm_S
    thmNames 1 2 2 .none .none
    (fun w tot _ T _ => (w.toFloat / tot.toFloat ≥ 0.33) && (T != .sort 0))
    (fun w tot _ _ => (w.toFloat / tot.toFloat ≥ 0.33))
    onlyInd

#check 1


def testSub_GH (onlyInd : Bool) (thmNames : Array Name) :=
  test_subSample_cvbGoalHyp_S
    thmNames 1 2 2 .none .none
    (fun w tot _ T _ => (w.toFloat / tot.toFloat ≥ 0.33) && (T != .sort 0))
    (fun w tot _ _ => (w.toFloat / tot.toFloat ≥ 0.33))
    onlyInd


#check 1

def testSub_samples (thmNames : Array Name) : MetaM Unit := do
  let env ← getEnv
  let preS ← mkPreProCongr
  let mut L1 := ← getLCtx
  let mut L2 := ← getLocalInstances
  let mut samples : ListProd4 SampleData (List FVarId) Expr (List Expr) := .nil
  for thmName in thmNames do
    let .some (.thmInfo I) := env.find? thmName | throwError "Bad name"
    let .mk p fvs l1 l2 ← LambdaLetTelescope I.value 0 L1 L2
    let .mk res _ l1 l2 ← sampleCoreBack preS .empty l1 l2 1 2 2 .none .none (.cons (.raw p) (fvs.map Expr.fvarId!).toList .nil) samples .nil
    samples := res
    L1 := l1
    L2 := l2
  samples := samples.foldl .nil (fun w x y z L => match w with | .induc .. => ListProd4.cons w x y z L | _ => L)
  withLCtx L1 L2 <| do
    samples.foldlM () (fun kind _ goal hyps _ => do
      IO.println "\nSample (back):"
      IO.println s! "Goal: {← ppExpr goal}"
      IO.println "Hyps:"
      hyps.foldlM (fun _ subp => do IO.println s!" · {← ppExpr subp}") ()
      IO.println s!"Kind: {← kind.pp}"
      )




#check 1

open List

theorem material_1' (l : List Nat) : l.dedup.dedup <+ l := by
  rw [dedup_idem]
  induction l with
  | nil =>
    dsimp
    apply Sublist.refl
  | _ =>
    apply dedup_sublist


theorem material_2_1' (l L : List Nat) : l.dedup.dedup.length + L.length ≤ (l ++ L).length:= by
  rw [dedup_idem]
  induction l with
  | nil =>
    dsimp
    rw [Nat.zero_add]
  | _ =>
    rw [length_append]
    apply Nat.add_le_add_right
    apply Sublist.length_le
    apply dedup_sublist


theorem material_2_2' (l L : List Nat) : l.dedup.dedup.length + L.length ≤ (l ++ L).length:= by
  rw [dedup_idem, length_append]
  apply Nat.add_le_add_right
  induction l with
  | nil =>
    dsimp
    apply Nat.le_refl
  | _ =>
    apply Sublist.length_le
    apply dedup_sublist


theorem material_3' (l : List Nat) (a b : Nat) (h : a = b) :
  (a :: b :: l).dedup.length ≤ (b :: l).length  := by
  apply Sublist.length_le
  rw [dedup_cons_of_mem]
  · apply dedup_sublist
  · rw [h]
    apply Mem.head


theorem material_4' (l : List Nat)
  (a : Nat) (h1 : a ∈ l.dedup) : (a :: l).dedup.length ≤ l.length := by
  apply Sublist.length_le
  have := dedup_sublist l
  rw [dedup_cons_of_mem]
  · exact this
  · apply Sublist.mem _ this
    exact h1


def thmNames' := #[`material_1', `material_2_1', `material_2_2', `material_3', `material_4']


-- #eval testSub_samples thmNames

-- #eval testSub_T false thmNames


tracing_mode .std
tracing_flags [(``test_backSample_cvbGoalHyp, TracingFlags.all),
               (`cvb_goal_hyp_genMain_subPat, TracingFlags.all),
               (`cvb_goal_hyp_genHyps, TracingFlags.all),
               ]

-- #eval testSub_GH false thmNames

#check 1

/-
↑ pattern ?testSam.0 ≤ ?testSam.0 doesn't seem to get deduplicated properly ...
-/
