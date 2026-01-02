
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Utils.Tracing

open Lean Meta



def test_1 : MetaM Unit := do
  mtracing
  mtrace on .zero when true with "first"
  match (← getEnv).find? `propext with
  | .none => pure ()
  | .some v =>
      mtrace on .one when true with s!"second {v.name}"
      pure ()

#eval test_1

#check 1

tracing_mode .std
tracing_flags [(`test_1,[.zero])]

#eval test_1

#check 1

tracing_flags [(`test_1,[.zero, .one])]

#eval test_1

#check 1


partial def test_2 (n : Nat) : MetaM Unit := do
  mtracing
  mtrace on .zero when true with s!"{n}"
  test_2 (n+1)

tracing_mode .hard
tracing_flags [(`test_2,[.zero, .one])]
-- #eval test_2 42



set_option trace.compiler.ir.result true in
def test_3 : Nat :=
  trace set TracingFlags.all in
  [1,2,3].foldl (fun R i =>
    trace on .zero with s!"trace type 1 : {i}" in
    trace on .one when (i%2 == 0) with s!"trace type 2 : {i}" in
    R + i
    ) 0

#eval test_3


set_option trace.compiler.ir.result true in
def test_4 : Nat :=
  trace set TracingFlags.none in
  [1,2,3].foldl (fun R i =>
    trace on .zero with s!"trace type 1 : {i}" in
    trace on .one when (i%2 == 0) with s!"trace type 2 : {i}" in
    R + i
    ) 0

#eval test_4
