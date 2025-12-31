
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Lean.Elab


set_option autoImplicit true

open Lean Meta Elab Term Command


def elabAndLoad (is : Array Name) (ts : Array Syntax) {α : Sort _} (k : Array Expr → TermElabM α) : TermElabM α :=
  let rec go (i : Nat) (done : Array Expr) : TermElabM α := do
    if i < ts.size
    then
      let todo := ts[i]!
      let ltx ← getLCtx
      let term ← elabTermAndSynthesize todo .none
      let name := is[i]!
      let ltx := ltx.addDecl (.cdecl i ⟨name⟩ name term .default .default)
      withLCtx ltx (← getLocalInstances) do
        go (i+1) (done.set! i term)
    else
      k done
  go 0 (Array.replicate ts.size (.bvar 42))

elab "With" "context" cs:("("ident ":" term")")* "and" "objects" ts:term,* "run" metam:ident : command => unsafe do
  let mut cts : Array Syntax := #[]
  let mut cis : Array Name := #[]
  for c in cs do
    match c.raw with
    | .node _ _ A =>
        cis := cis.push (Syntax.getId A[1]!)
        cts := cts.push A[3]!
    | _ => throwError s!"Unexpected syntax at context {c}, expecting (x : T)"
  let ts := ts.getElems.raw
  liftTermElabM do
    elabAndLoad cis cts <| fun elabedContext => do
      let mut Ts : Array Expr := #[]
      for t in ts do
        let term ← elabTermAndSynthesize t .none
        Ts := Ts.push term
      let action ← evalConst (Array Expr → Array Expr → MetaM Unit) (metam.getId)
      action elabedContext Ts


def elabAndLoadLet (is : Array Name) (ts : Array Syntax) (vs : Array Syntax) {α : Sort _} (k : Array Expr → Array Expr → TermElabM α) : TermElabM α :=
  let rec go (i : Nat) (doneT doneV : Array Expr) : TermElabM α := do
    if i < ts.size
    then
      let todoT := ts[i]!
      let todoV := vs[i]!
      let ltx ← getLCtx
      let termT ← elabTermAndSynthesize todoT .none
      let termV ← elabTermAndSynthesize todoV .none
      let name := is[i]!
      let ltx := ltx.addDecl (.ldecl i ⟨name⟩ name termT termV false .default)
      withLCtx ltx (← getLocalInstances) do
        go (i+1) (doneT.set! i termT) (doneV.set! i termV)
    else
      k doneT doneV
  go 0 (Array.replicate ts.size (.bvar 42)) (Array.replicate ts.size (.bvar 42))
