

import LeanGrow.Src.SampleGenScore.Delab.WfBrec

import Mathlib.SetTheory.ZFC.VonNeumann

import Mathlib.Combinatorics.Enumerative.DyckWord

open Lean Meta


def test_main_sample (n : Name) : MetaM Unit := do
  let .some info := (← getEnv).find? n | throwError "Bad name"
  lambdaTelescope info.value! <| fun _ b => do
    let h := b.getAppFn'
    let isit ← delabSample_WfBrec_core h
    IO.println s!"isit: {isit}"


def test_main_dig (n : Name) : MetaM Unit := do
  let .some info := (← getEnv).find? n | throwError "Bad name"
  lambdaTelescope info.value! <| fun _ b => do
    let h := b.getAppFn'
    let as := b.getAppArgs
    let .mk sub l1 l2 ← delabDig_WfBrec_core [] h as (← getLCtx) (← getLocalInstances)
    match sub with
    | .none => IO.println "Not found"
    | .some sub lifts =>
        withLCtx l1 l2 <| do
          IO.println "Lifts"
          for li in lifts do
            IO.println s!" {li.name} : {← ppExpr <| ← li.getType}"
          IO.println "Sub"
          for nex in sub do
            IO.println s!"Type: {← ppExpr (← inferType nex)}\nTerm: {← ppExpr ( nex)}"


#print Nat.add_comm

-- #eval test_main_sample `Nat.add_comm

-- #eval test_main_dig `Nat.add_comm


#print Nat.mul_assoc

-- #eval test_main_sample `Nat.mul_assoc

-- #eval test_main_dig `Nat.mul_assoc


#print List.mem_of_elem_eq_true

-- #eval test_main_sample `List.mem_of_elem_eq_true

-- #eval test_main_dig `List.mem_of_elem_eq_true

#print ZFSet.isTransitive_vonNeumann

-- tracing_mode .std
-- tracing_flags [(`delabDig_WfBrec_core, TracingFlags.all)]

-- #eval test_main_sample `ZFSet.isTransitive_vonNeumann

-- #eval test_main_dig `ZFSet.isTransitive_vonNeumann


#print DyckWord.le_add_self

-- #eval test_main_sample `DyckWord.le_add_self

-- #eval test_main_dig `DyckWord.le_add_self
