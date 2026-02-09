

import LeanGrow.Src.SampleGenScore.Sample

import Mathlib.Data.List.Dedup


open Lean Meta

set_option linter.style.longLine false

def testNoDelZet_F (printLift? : Bool) (thmName : Name) (depthDig depthStart depthStop : Nat) : MetaM Unit := do
  let .some (.thmInfo I) := (← getEnv).find? thmName | throwError "Bad name"
  lambdaTelescope I.value <| fun fvs p => do
    let preS ← mkPreProCongr
    let .mk res l1 l2 ← sampleCoreForw preS (← getLCtx) (← getLocalInstances) false depthDig depthStart depthStop .none .none (.cons (.raw p) (fvs.map Expr.fvarId!).toList .nil) .nil
    withLCtx l1 l2 <| do
      res.foldlM () (fun kind fvs goal hyps _ => do
        IO.println "\nSample (forw):\nLifted:"
        if printLift?
          then fvs.foldlM (fun _ fv => do IO.println s!" {← fv.getUserName} : {← ppExpr (← fv.getType)}") ()
        IO.println s! "Goal: {← ppExpr goal}"
        IO.println "Hyps:"
        hyps.foldlM (fun _ subp => do IO.println s!" · {← ppExpr subp}") ()
        IO.println s!"Kind: {repr kind}"
        )

#check 1

def testDelZet_F (printLift? : Bool) (thmName : Name) (depthDig depthStart depthStop deltaFuel zetaFuel : Nat) : MetaM Unit := do
  let .some (.thmInfo I) := (← getEnv).find? thmName | throwError "Bad name"
  lambdaTelescope I.value <| fun fvs p => do
    let preS ← mkPreProCongr
    let .mk res l1 l2 ← sampleCoreForw preS (← getLCtx) (← getLocalInstances) false depthDig depthStart depthStop deltaFuel zetaFuel (.cons (.raw p) (fvs.map Expr.fvarId!).toList .nil) .nil
    withLCtx l1 l2 <| do
      res.foldlM () (fun kind fvs goal hyps _ => do
        IO.println "\nSample (forw):\nLifted:"
        if printLift?
          then fvs.foldlM (fun _ fv => do IO.println s!" {← fv.getUserName} : {← ppExpr (← fv.getType)}") ()
        IO.println s! "Goal: {← ppExpr goal}"
        IO.println "Hyps:"
        hyps.foldlM (fun _ subp => do IO.println s!" · {← ppExpr subp}") ()
        IO.println s!"Kind: {repr kind}"
        )

#check 1

def testNoDelZet_wH_F (printLift? : Bool) (thmName : Name) (depthDig depthStart depthStop : Nat) : MetaM Unit := do
  let .some (.thmInfo I) := (← getEnv).find? thmName | throwError "Bad name"
  lambdaTelescope I.value <| fun fvs p => do
    let preS ← mkPreProCongr
    let .mk res l1 l2 ← sampleCoreForw preS (← getLCtx) (← getLocalInstances) true depthDig depthStart depthStop .none .none (.cons (.raw p) (fvs.map Expr.fvarId!).toList .nil) .nil
    withLCtx l1 l2 <| do
      res.foldlM () (fun kind fvs goal hyps _ => do
        IO.println "\nSample (forw with hyps):\nLifted:"
        if printLift?
          then fvs.foldlM (fun _ fv => do IO.println s!" {← fv.getUserName} : {← ppExpr (← fv.getType)}") ()
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


-- #exit

#check List.dedup_sublist
#check List.dedup_idem
#check List.length_append
#check List.length_drop
#check List.Sublist.length_le

open List


theorem testProof_F_1 (l : List Nat) : l.dedup.dedup <+ l := by
  rw [dedup_idem]
  apply dedup_sublist


-- #eval testNoDelZet_F true `testProof_F_1 1 1 1
-- list is

-- #eval testDelZet_F true `testProof_F_1 1 1 1 1 1
-- ↑ has pairwise due to thms being wrappers arround pwFilter
#check List.Nodup

theorem testProof_F_2 (l L : List Nat) : l.dedup.dedup.length + L.length ≤ (l ++ L).length:= by
  rw [dedup_idem, length_append]
  apply Nat.add_le_add_right
  apply Sublist.length_le
  apply dedup_sublist

-- #eval testNoDelZet_F true `testProof_F_2 1 1 2

-- #eval testNoDelZet_F true `testProof_F_2 1 2 2

-- #eval testNoDelZet_F true `testProof_F_2 1 3 3

-- #eval testDelZet_F true `testProof_F_2 1 2 2 1 1

-- #eval testDelZet_F true `testProof_F_2 1 2 2 2 2

-- #eval testNoDelZet_wH_F true `testProof_F_2 1 1 2

-- #eval testNoDelZet_wH_F true `testProof_F_2 1 2 2


theorem testProof_F_3 (l : List Nat) (a b : Nat) (h : a = b) :
  (a :: b :: l).dedup.length ≤ (b :: l).length  := by
  apply Sublist.length_le
  rw [dedup_cons_of_mem]
  · apply dedup_sublist
  · rw [h]
    apply Mem.head


-- tracing_mode .std
-- tracing_flags [(`delabTopForw, TracingFlags.all), (`sampleHypsCore.go, TracingFlags.all),]

-- #eval testNoDelZet_F true `testProof_F_3 1 1 2

-- #eval testNoDelZet_F true `testProof_F_3 1 2 2

-- #eval testNoDelZet_F true `testProof_F_3 1 3 3


open List
theorem testProof_F_4 {xs ys : List Nat} (h : xs ⊆ ys) :
    dedup (xs ++ ys) = dedup ys := by
  rw [List.dedup_append, Subset.union_eq_right (List.Subset.trans h <| subset_dedup _)]

-- #eval testNoDelZet_F true `testProof_F_4 1 1 1
