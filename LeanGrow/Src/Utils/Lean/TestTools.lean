
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Lean.Elab
import LeanGrow.Src.Utils.Lean.MetaAPI


open Lean Meta Elab Term Command

@[inline, specialize]
def elabAndLoad (i : Nat) (is : Name) (ts : Syntax) {α : Sort _} (k : Expr → Expr → TermElabM α) : TermElabM α := do
  let todo := ts
  let term ← elabTermAndSynthesize todo .none
  let name := is
  let fv := (.fvar ⟨name⟩)
  let ltx ← getLCtx
  let linst ← getLocalInstances
  let ltx := ltx.addDecl (.cdecl i ⟨name⟩ name term .default .default)
  let linst ← (do
    if let some c ← isClass? term
    then
      return linst.push { className := c, fvar := fv }
    else
      return linst)
  withLCtx ltx linst do
    k term fv

#check 1

def elabAndLoadLet (i : Nat) (is : Name) (ts : Syntax) (vs : Syntax) {α : Sort _} (k : Expr → Expr → TermElabM α) : TermElabM α := do
  let todoT := ts
  let todoV := vs
  let termT ← elabTermAndSynthesize todoT .none
  let termV ← elabTermAndSynthesize todoV .none
  let name := is
  let fv := (.fvar ⟨name⟩)
  let ltx ← getLCtx
  let linst ← getLocalInstances
  let ltx := ltx.addDecl (.ldecl i ⟨name⟩ name termT termV false .default)
  let linst ← (do
    if let some c ← isClass? termT
    then
      return linst.push { className := c, fvar := fv }
    else
      return linst)
  withLCtx ltx linst do
    k termT fv


#check 1



declare_syntax_cat lg_lam_let

syntax "("ident ":" term")" : lg_lam_let

syntax "("ident ":" term ":" term")" : lg_lam_let


def elabForTest (i : Nat) (cs : TSyntaxArray `lg_lam_let) (doneT doneFv : Array Expr)
  {α : Sort _} (k : Array Expr → Array Expr → TermElabM α) : TermElabM α := do
    if i < cs.size
    then
      let c := cs[i]!
      match c with
      | `(lg_lam_let| ($id : $ter)) => elabAndLoad i id.getId ter <| fun T fv => elabForTest (i+1) cs (doneT.push T) (doneFv.push fv) k
      | `(lg_lam_let| ($id : $ter : $val)) => elabAndLoadLet i id.getId ter val <| fun T fv => elabForTest (i+1) cs (doneT.push T) (doneFv.push fv) k
      | _ => throwError "Unexpected syntax ..."
    else
      k doneT doneFv

#check 1


elab "With" "context" cs:lg_lam_let* "and" "objects" ts:term,* "run" metam:ident : command => unsafe do
  let ts := ts.getElems.raw
  liftTermElabM do
    elabForTest 0 cs #[] #[] <| fun _ fv => do
      let mut Ts : Array Expr := #[]
      for t in ts do
        let term ← elabTermAndSynthesize t .none
        Ts := Ts.push term
      let action ← evalConst (Array Expr → Array Expr → MetaM Unit) (metam.getId)
      clearMvarAssignments
      action fv Ts
