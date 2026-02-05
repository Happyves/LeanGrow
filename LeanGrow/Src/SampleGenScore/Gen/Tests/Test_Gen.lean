

import LeanGrow.Src.SampleGenScore.Gen.TestTools_SampleGen

import Mathlib.Data.List.Dedup

open Lean Meta


def test_T (thmNames : Array Name) :=
  test_backSample_cvbThm_S
    thmNames 1 2 2 .none .none
    (fun w tot _ T _ => (w.toFloat / tot.toFloat ≥ 0.33) && (T != .sort 0))
    (fun w tot _ _ => (w.toFloat / tot.toFloat ≥ 0.33))

#check 1


def test_GH (thmNames : Array Name) :=
  test_backSample_cvbGoalHyp_S
    thmNames 1 2 2 .none .none
    (fun w tot _ T _ => (w.toFloat / tot.toFloat ≥ 0.33) && (T != .sort 0))
    (fun w tot _ _ => (w.toFloat / tot.toFloat ≥ 0.33))


#check 1

def test_samples (thmNames : Array Name) : MetaM Unit := do
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
  withLCtx L1 L2 <| do
    samples.foldlM () (fun kind _ goal hyps _ => do
      IO.println "\nSample (back):"
      IO.println s! "Goal: {← ppExpr goal}"
      IO.println "Hyps:"
      hyps.foldlM (fun _ subp => do IO.println s!" · {← ppExpr subp}") ()
      IO.println s!"Kind: {repr kind}"
      )




#check List.dedup_sublist
#check List.dedup_idem
#check List.length_append
#check List.length_drop
#check List.Sublist.length_le

open List

theorem material_1 (l : List Nat) : l.dedup.dedup <+ l := by
  rw [dedup_idem]
  apply dedup_sublist


theorem material_2_1 (l L : List Nat) : l.dedup.dedup.length + L.length ≤ (l ++ L).length:= by
  rw [dedup_idem]
  rw [length_append]
  apply Nat.add_le_add_right
  apply Sublist.length_le
  apply dedup_sublist


theorem material_2_2 (l L : List Nat) : l.dedup.dedup.length + L.length ≤ (l ++ L).length:= by
  rw [dedup_idem, length_append]
  apply Nat.add_le_add_right
  apply Sublist.length_le
  apply dedup_sublist


theorem material_3 (l : List Nat) (a b : Nat) (h : a = b) :
  (a :: b :: l).dedup.length ≤ (b :: l).length  := by
  apply Sublist.length_le
  rw [dedup_cons_of_mem]
  · apply dedup_sublist
  · rw [h]
    apply Mem.head


theorem material_4 (l : List Nat)
  (a : Nat) (h1 : a ∈ l.dedup) : (a :: l).dedup.length ≤ l.length := by
  apply Sublist.length_le
  have := dedup_sublist l
  rw [dedup_cons_of_mem]
  · exact this
  · apply Sublist.mem _ this
    exact h1


def thmNames := #[`material_1, `material_2_1, `material_2_2, `material_3, `material_4]

--samples
-- #eval test_samples thmNames

tracing_mode .std
tracing_flags [(`test_backSample_cvbThm, TracingFlags.all),
               (`cvb_thms_genGoal, TracingFlags.all),
               (`cvb_thms_genHyps, TracingFlags.all),
               ]


-- #eval test_T thmNames

/-

FIX:
At `cvb_thms_genMain`, maintain sample-types and cleaned-types.
Generalisation should use sample-types and emit sample-types, as it doesn't
delete any entries. Lnode garbade collection should take both types,
and set the new cleaned-types, where the new tree will reference the
cleaned-types.

Bring fixes to subpats and conjecturable


Generalisation:
- Frequency of type among all types, not just infrequent ones ?
- Issue with generalisation for rewrite goals (for example): generalised version
  may not contain patern anymore, so rw wouldn't apply ...
  Long term:
    - track position of patterns, and prohibit generalising them ?
    - separate pattern and term its in, and generalise each separately ?

-/
tracing_mode .std
tracing_flags [(``test_backSample_cvbGoalHyp, TracingFlags.all),
               (`cvb_goal_hyp_genGoal, TracingFlags.all),
               (`cvb_goal_hyp_genHyps, TracingFlags.all),
               ]

-- #eval test_GH thmNames
