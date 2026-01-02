

/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Utils.LeanGrow.Expr


open Lean Meta Elab Term Command

@[inline, specialize]
def elabAndLoad_G (i gu_idx : Nat) (is : Name) (ts : Syntax)
  (trans : NameMap Name) (deps : Array (List LocalDecl))
  {α : Sort _} (k : Expr → Expr → NameMap Name → Array (List LocalDecl) → TermElabM α) : TermElabM α := do
  let todo := ts
  let term ← elabTermAndSynthesize todo .none
  let name := is
  let tterm := term.onAllSubtermsTR (fun
        | d@(.fvar fid) =>
            match trans.find? fid.name with
            | .none => d
            | .some new =>
                match new with
                | .num (.num N _) _ =>
                    if N == `t then .fvar ⟨new⟩ else .mvar ⟨new⟩
                | _ => .fvar ⟨new⟩
        | x => x
        )
  let rep := (.num `g gu_idx)
  let trans := trans.insert name rep
  let ltx ← getLCtx
  let linst ← getLocalInstances
  let ltx := ltx.addDecl (.cdecl i ⟨name⟩ name term .default .default)
  let rdec := (.cdecl i ⟨rep⟩ rep tterm .default .default)
  let ltx := ltx.addDecl rdec
  let fv := (.fvar ⟨name⟩)
  let linst ← (do
    if let some c ← isClass? term
    then
      return linst.push { className := c, fvar := fv }
    else
      return linst)
  let fv := (.fvar ⟨rep⟩)
  let linst ← (do
    if let some c ← isClass? tterm
    then
      return linst.push { className := c, fvar := fv }
    else
      return linst)
  let depFvs := tterm.getGUFVarsIds
  let deps := depFvs.foldl (fun D ⟨fv⟩ =>
    match fv with
    | .num _ idx => D.modify idx (fun l => rdec :: l)
    | _ => D
    ) deps
  withLCtx ltx linst do
    k tterm fv trans (deps.push [])

#check 1


@[inline, specialize]
def elabAndLoad_U (i gu_idx : Nat) (is : Name) (ts vs : Syntax)
  (trans : NameMap Name) (deps : Array (List LocalDecl))
  {α : Sort _} (k : Expr → Expr → NameMap Name → Array (List LocalDecl) → TermElabM α) : TermElabM α := do
  let todoT := ts
  let todoV := vs
  let termT ← elabTermAndSynthesize todoT .none
  let termV ← elabTermAndSynthesize todoV .none
  let name := is
  let ttermT := termT.onAllSubtermsTR (fun
        | d@(.fvar fid) =>
            match trans.find? fid.name with
            | .none => d
            | .some new =>
                match new with
                | .num (.num N _) _ =>
                    if N == `t then .fvar ⟨new⟩ else .mvar ⟨new⟩
                | _ => .fvar ⟨new⟩
        | x => x
        )
  let ttermV := termV.onAllSubtermsTR (fun
        | d@(.fvar fid) =>
            match trans.find? fid.name with
            | .none => d
            | .some new =>
                match new with
                | .num (.num N _) _ =>
                    if N == `t then .fvar ⟨new⟩ else .mvar ⟨new⟩
                | _ => .fvar ⟨new⟩
        | x => x
        )
  let rep := (.num `u gu_idx)
  let trans := trans.insert name rep
  let ltx ← getLCtx
  let linst ← getLocalInstances
  let ltx := ltx.addDecl (.ldecl i ⟨name⟩ name termT termV false .default)
  let rdec := (.ldecl i ⟨rep⟩ rep ttermT ttermV false .default)
  let ltx := ltx.addDecl rdec
  let fv := (.fvar ⟨name⟩)
  let linst ← (do
    if let some c ← isClass? termT
    then
      return linst.push { className := c, fvar := fv }
    else
      return linst)
  let fv := (.fvar ⟨rep⟩)
  let linst ← (do
    if let some c ← isClass? ttermT
    then
      return linst.push { className := c, fvar := fv }
    else
      return linst)
  let depFvs := ttermT.getGUFVarsIds
  let deps := depFvs.foldl (fun D ⟨fv⟩ =>
    match fv with
    | .num _ idx => D.modify idx (fun l => rdec :: l)
    | _ => D
    ) deps
  withLCtx ltx linst do
    k ttermT fv trans (deps.push [])

#check 1


@[inline, specialize]
def elabAndLoad_T (i t_idx pos : Nat) (is : Name) (ts : Syntax) (trans : NameMap Name) {α : Sort _} (k : Expr → Expr → NameMap Name → TermElabM α) : TermElabM α := do
  let todo := ts
  let term ← elabTermAndSynthesize todo .none
  let name := is
  let tterm := term.onAllSubtermsTR (fun
        | d@(.fvar fid) =>
            match trans.find? fid.name with
            | .none => d
            | .some new =>
                match new with
                | .num (.num N _) _ =>
                    if N == `t then .fvar ⟨new⟩ else .mvar ⟨new⟩
                | _ => .fvar ⟨new⟩
        | x => x
        )
  let rep := tnode t_idx pos
  let trans := trans.insert name rep
  let ltx ← getLCtx
  let linst ← getLocalInstances
  let ltx := ltx.addDecl (.cdecl i ⟨name⟩ name term .default .default)
  let ltx := ltx.addDecl (.cdecl i ⟨rep⟩ rep tterm .default .default)
  let fv := (.fvar ⟨name⟩)
  let linst ← (do
    if let some c ← isClass? term
    then
      return linst.push { className := c, fvar := fv }
    else
      return linst)
  let fv := (.fvar ⟨rep⟩)
  let linst ← (do
    if let some c ← isClass? tterm
    then
      return linst.push { className := c, fvar := fv }
    else
      return linst)
  withLCtx ltx linst do
    k tterm fv trans


#check 1

@[inline, specialize]
def elabAndLoad_L (i l_idx pos : Nat) (module is : Name) (ts : Syntax) (trans : NameMap Name) {α : Sort _} (k : Expr → Expr → NameMap Name → TermElabM α) : TermElabM α := do
  let todo := ts
  let term ← elabTermAndSynthesize todo .none
  let name := is
  let tterm := term.onAllSubtermsTR (fun
        | d@(.fvar fid) =>
            match trans.find? fid.name with
            | .none => d
            | .some new =>
                match new with
                | .num (.num N _) _ =>
                    if N == `t then .fvar ⟨new⟩ else .mvar ⟨new⟩
                | _ => .fvar ⟨new⟩
        | d@(.mvar fid) =>
            match trans.find? fid.name with
            | .none => d
            | .some new => .mvar ⟨new⟩
        | x => x
        )
  let rep := lnode module l_idx pos
  let trans := trans.insert name rep
  let _ ← mkMvarStdIndexNoCoE name term i
  let mv ← mkMvarStdIndexNoCoE rep tterm i
  k tterm mv trans

#check 1



declare_syntax_cat lg_test

syntax "g("ident ":" term")" : lg_test

syntax "u("ident ":" term ":" term")" : lg_test

syntax "t("num ":" num ":" ident ":" term")" : lg_test

syntax "l("ident ":" num ":" num ":" ident ":" term")" : lg_test


def elabForTest (i gu_idx : Nat) (cs : TSyntaxArray `lg_test)
  (guT gu tT t lT l : Array Expr)
  (trans : NameMap Name) (deps : Array (List LocalDecl))
  {α : Sort _} (k : Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array (List LocalDecl) → TermElabM α) : TermElabM α := do
    if i < cs.size
    then
      let c := cs[i]!
      match c with
      | `(lg_test| g($id : $ter)) =>
          elabAndLoad_G i gu_idx id.getId ter trans deps <| fun T fv trans deps =>
            elabForTest (i+1) (gu_idx+1) cs (guT.push T) (gu.push fv) tT t lT l trans deps k
      | `(lg_test| u($id : $ter : $val)) =>
          elabAndLoad_U i gu_idx id.getId ter val trans deps <| fun T fv trans deps =>
            elabForTest (i+1) (gu_idx+1) cs (guT.push T) (gu.push fv) tT t lT l trans deps k
      | `(lg_test| t($ix : $po : $id : $ter)) =>
          elabAndLoad_T i ix.getNat po.getNat id.getId ter trans <| fun T fv trans =>
            elabForTest (i+1) gu_idx cs guT gu (tT.push T) (t.push fv) lT l trans deps k
      | `(lg_test| l($mod : $ix : $po : $id : $ter)) =>
          elabAndLoad_L i ix.getNat po.getNat mod.getId id.getId ter trans <| fun T fv trans =>
            elabForTest (i+1) (gu_idx+1) cs guT gu tT t (lT.push T) (l.push fv) trans deps k
      | _ => throwError "Unexpected syntax ..."
    else
      k guT gu tT t lT l deps

#check 1

elab "With" "context" cs:lg_test* "and" "objects" ts:term,* "run" metam:ident : command => unsafe do
  let ts := ts.getElems.raw
  liftTermElabM do
    elabForTest 0 0 cs #[] #[] #[] #[] #[] #[] {} #[] <| fun guT gu tT t lT l deps => do
      let mut Ts : Array Expr := #[]
      for t in ts do
        let term ← elabTermAndSynthesize t .none
        Ts := Ts.push term
      let action ← evalConst ( Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array (List LocalDecl) → MetaM Unit) (metam.getId)
      action guT gu tT t lT l deps
