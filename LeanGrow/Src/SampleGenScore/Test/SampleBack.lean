

import LeanGrow.Src.SampleGenScore.Sample

import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Lemmas

open Lean Meta

set_option linter.style.longLine false

def testNoDelZet_B (printLift? : Bool) (thmName : Name) (depthDig depthStart depthStop : Nat) : MetaM Unit := do
  let .some (.thmInfo I) := (← getEnv).find? thmName | throwError "Bad name"
  lambdaTelescope I.value <| fun fvs p => do
    let preS ← mkPreProCongr
    let .mk res _ l1 l2 ← sampleCoreBack preS .empty (← getLCtx) (← getLocalInstances) depthDig depthStart depthStop .none .none (.cons (.raw p) (fvs.map Expr.fvarId!).toList .nil) .nil .nil
    withLCtx l1 l2 <| do
      res.foldlM () (fun kind fvs goal hyps _ => do
        IO.println "\nSample (back):\nLifted:"
        if printLift?
          then fvs.foldlM (fun _ fv => do IO.println s!" {← fv.getUserName} : {← ppExpr (← fv.getType)}") ()
        IO.println s! "Goal: {← ppExpr goal}"
        IO.println "Hyps:"
        hyps.foldlM (fun _ subp => do IO.println s!" · {← ppExpr subp}") ()
        IO.println s!"Kind: {← kind.pp}"
        )

#check 1

def testDelZet_B (printLift? : Bool) (thmName : Name) (depthDig depthStart depthStop deltaFuel zetaFuel : Nat) : MetaM Unit := do
  let .some (.thmInfo I) := (← getEnv).find? thmName | throwError "Bad name"
  lambdaTelescope I.value <| fun fvs p => do
    let preS ← mkPreProCongr
    let .mk res _ l1 l2 ← sampleCoreBack preS .empty (← getLCtx) (← getLocalInstances) depthDig depthStart depthStop deltaFuel zetaFuel (.cons (.raw p) (fvs.map Expr.fvarId!).toList .nil) .nil .nil
    withLCtx l1 l2 <| do
      res.foldlM () (fun kind fvs goal hyps _ => do
        IO.println "\nSample (back):\nLifted:"
        if printLift?
          then fvs.foldlM (fun _ fv => do IO.println s!" {← fv.getUserName} : {← ppExpr (← fv.getType)}") ()
        IO.println s! "Goal: {← ppExpr goal}"
        IO.println "Hyps:"
        hyps.foldlM (fun _ subp => do IO.println s!" · {← ppExpr subp}") ()
        IO.println s!"Kind: {← kind.pp}"
        )

#check 1



#check List.dedup_sublist
#check List.dedup_idem
#check List.length_append
#check List.length_drop
#check List.Sublist.length_le

open List


theorem testProof_B_1 (l : List Nat) : l.dedup.dedup <+ l := by
  rw [dedup_idem]
  apply dedup_sublist


-- #eval testNoDelZet_B true `testProof_B_1 1 1 1

-- #eval testDelZet_B true `testProof_B_1 1 1 1 1 1
-- ↑ has pairwise due to thms being wrappers arround pwFilter
#check List.Nodup

theorem testProof_B_2 (l L : List Nat) : l.dedup.dedup.length + L.length ≤ (l ++ L).length:= by
  rw [dedup_idem, length_append]
  apply Nat.add_le_add_right
  apply Sublist.length_le
  apply dedup_sublist

-- #eval testNoDelZet_B true `testProof_B_2 1 1 2

-- #eval testNoDelZet_B true `testProof_B_2 1 2 2

-- #eval testNoDelZet_B true `testProof_B_2 1 3 3

-- #eval testDelZet_B true `testProof_B_2 1 2 2 1 1

-- #eval testDelZet_B true `testProof_B_2 1 2 2 2 2


theorem testProof_B_3 (l : List Nat) (a b : Nat) (h : a = b) :
  (a :: b :: l).dedup.length ≤ (b :: l).length  := by
  apply Sublist.length_le
  rw [dedup_cons_of_mem]
  · apply dedup_sublist
  · rw [h]
    apply Mem.head



-- #eval testNoDelZet_B true `testProof_B_3 1 1 2

-- #eval testNoDelZet_B true `testProof_B_3 1 2 2

-- #eval testNoDelZet_B true `testProof_B_3 1 3 3

open List
theorem testProof_B_4 {xs ys : List Nat} (h : xs ⊆ ys) :
    dedup (xs ++ ys) = dedup ys := by
  rw [List.dedup_append, Subset.union_eq_right (List.Subset.trans h <| subset_dedup _)]

-- tracing_mode .std
-- tracing_flags [(`sampleHypsCore.inner, TracingFlags.all),
--                (`sampleHypsCore.go, TracingFlags.all),
--                (`delabSample, TracingFlags.all),
--                (`delabDig, TracingFlags.all),
--                (`digExpr.inner, TracingFlags.all),
--                (`digExpr.go, TracingFlags.all),]


-- #eval testNoDelZet_B true `testProof_B_4 1 1 1


open List

theorem injOn_insertIdx_index_of_notMem' (x : α) (l : List α) (hx : x ∉ l)
    : Set.InjOn (fun k => l.insertIdx k x) { n | n ≤ l.length } := by
  intro n hn m hm h
  induction l generalizing n m with
  | nil =>
    simp_all [Set.mem_singleton_iff, Set.setOf_eq_eq_singleton, length]
  | cons hd tl IH =>
    simp only [length, Set.mem_setOf_eq] at hn hm
    simp only [mem_cons, not_or] at hx
    cases n <;> cases m
    · rfl
    · simp [hx.left] at h
    · simp [Ne.symm hx.left] at h
    · simp only [insertIdx_succ_cons, cons.injEq, true_and] at h
      rw [Nat.succ_inj]
      refine IH hx.right ?_ ?_ h
      · simpa [Nat.succ_le_succ_iff] using hn
      · simpa [Nat.succ_le_succ_iff] using hm

#print injOn_insertIdx_index_of_notMem'


-- tracing_mode .std
-- tracing_flags [(`sampleHypsCore.inner, TracingFlags.all),
--                (`sampleHypsCore.go, TracingFlags.all),
--                (`delabSample, TracingFlags.all),
--                (`delabDig, TracingFlags.all),
--                (`digExpr.inner, TracingFlags.all),
--                (`digExpr.go, TracingFlags.all),
--                (`delabTopBack, TracingFlags.all),
--                (`delabSample_AssertDefineRevert_top, TracingFlags.all),
--                (`delab_simpGoal, TracingFlags.all),
--                (`sampleCoreBack, TracingFlags.all),
--                ]


-- #eval testNoDelZet_B false `injOn_insertIdx_index_of_notMem' 1 2 2
-- To fix ↑ : fix undesired Eq.trans in samples
