

import LeanGrow.Src.Caching.Formating.Process

import Mathlib.Data.List.Dedup

open Lean Meta


def test (n : Name) : MetaM Unit := do
  let .some dec := (← getEnv).find? n | throwError "aahh 1"
  let .mk _ thms l1 l2 ← processForCache `dummyMod 42 dec
  withLCtx l1 l2 <| do
    thms.foldlM () <| fun _ thm _ => do
      IO.println s!"\nTheorem {thm.name}"
      IO.println s!"Goal {← ppExpr thm.goal}"
      IO.println s!"Hyptypes {← thm.hypsTypes.mapM ppExpr}"
      IO.println s!"Sinks {thm.sinks}"
      IO.println s!"LevelNum {thm.lvlParamsNum}"
      IO.println s!"lDepth {thm.mctx.lDepth.map (fun (x,y) => (x.name,y))}"
      IO.println s!"mvDecls {← thm.mctx.decls.mapM (fun (x,y) => do return (x.name, ← ppExpr y.type))}"


#check 1

#eval test ``List.mem_append_left
