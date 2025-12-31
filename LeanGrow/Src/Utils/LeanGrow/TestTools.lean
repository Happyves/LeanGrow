

/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrowBeta.Utils.Lean.TestTools
import LeanGrowBeta.Utils.Lean.Expr.Basic

set_option autoImplicit true

open Lean Meta Elab Term Command


def elabAndLoadGTNode (pre : Name) (count : Nat) (trans : NameMap Name) (is : Array Name) (ts : Array Syntax)
  {α : Sort _} (k : Array Expr → Nat → NameMap Name → TermElabM α) : TermElabM α :=
  let rec go (i c : Nat) (done : Array Expr) (trans : NameMap Name) : TermElabM α := do
    if i < ts.size
    then
      let todo := ts[i]!
      let ltx ← getLCtx
      let term ← elabTermAndSynthesize todo .none
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
      let name := is[i]!
      let rep := (.num pre c)
      let trans := trans.insert name rep
      let ltx := ltx.addDecl (.cdecl i ⟨name⟩ name term .default .default)
      let ltx := ltx.addDecl (.cdecl i ⟨rep⟩ rep tterm .default .default)
      withLCtx ltx (← getLocalInstances) do
        go (i+1) (c+1) (done.set! i (.fvar ⟨rep⟩)) trans
    else
      k done c trans
  go 0 count (Array.replicate ts.size (.bvar 42)) trans


def elabAndLoadLNode (pre : Name) (count : Nat) (trans : NameMap Name) (is : Array Name) (ts : Array Syntax)
  {α : Sort _} (k : Array Expr → Nat → NameMap Name → TermElabM α) : TermElabM α :=
  let rec go (i c : Nat) (done : Array Expr) (trans : NameMap Name) : TermElabM α := do
    if i < ts.size
    then
      let todo := ts[i]!
      let ltx ← getLCtx
      let term ← elabTermAndSynthesize todo .none
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
      let name := is[i]!
      let rep := (.num pre c)
      let trans := trans.insert name rep
      let ltx := ltx.addDecl (.cdecl i ⟨name⟩ name term .default .default)
      let mv ← mkMvarStdIndexWiCoE rep tterm 0 (← getLCtx) (← getLocalInstances)
      withLCtx ltx (← getLocalInstances) do
        go (i+1) (c+1) (done.set! i mv) trans
    else
      k done c trans
  go 0 count (Array.replicate ts.size (.bvar 42)) trans



def elabAndLoadUNode (count : Nat) (trans : NameMap Name) (is : Array Name) (ts vs: Array Syntax)
  {α : Sort _} (k : Array Expr → Nat → NameMap Name → TermElabM α) : TermElabM α :=
  let rec go (i c : Nat) (done : Array Expr) (trans : NameMap Name) : TermElabM α := do
    if i < ts.size
    then
      let todoT := ts[i]!
      let todoV := vs[i]!
      let ltx ← getLCtx
      let termT ← elabTermAndSynthesize todoT .none
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
      let termV ← elabTermAndSynthesize todoV .none
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
      let name := is[i]!
      let rep := (.num `u c)
      let trans := trans.insert name rep
      let ltx := ltx.addDecl (.ldecl i ⟨name⟩ name termT termV false .default)
      let ltx := ltx.addDecl (.ldecl i ⟨rep⟩ rep ttermT ttermV false .default)
      withLCtx ltx (← getLocalInstances) do
        go (i+1) (c+1) (done.set! i (.fvar ⟨rep⟩)) trans
    else
      k done c trans
  go 0 count (Array.replicate ts.size (.bvar 42)) trans




/-
**Deficiencies of ↓**
- gnodes can't depend on unodes ...

-/


elab  "With" "gnodes" gs:("("ident ":" term")")*
      "and" "unodes" us:("("ident ":" term ":" term")")*
      "and" "tnodes" ts:("("ident ":" term")")*
      "and" "objects" os:term,*
      "run" metam:ident : command => unsafe do
  let mut gts : Array Syntax := #[]
  let mut gis : Array Name := #[]
  for c in gs do
    match c.raw with
    | .node _ _ A =>
        gis := gis.push (Syntax.getId A[1]!)
        gts := gts.push A[3]!
    | _ => throwError s!"Unexpected syntax at context {c}, expecting (x : T)"
  let mut uts : Array Syntax := #[]
  let mut uvs : Array Syntax := #[]
  let mut uis : Array Name := #[]
  for c in us do
    match c.raw with
    | .node _ _ A =>
        uis := uis.push (Syntax.getId A[1]!)
        uts := uts.push A[3]!
        uvs := uvs.push A[5]!
    | _ => throwError s!"Unexpected syntax at context {c}, expecting (x : T : V)"
  let mut tts : Array Syntax := #[]
  let mut tis : Array Name := #[]
  for c in ts do
    match c.raw with
    | .node _ _ A =>
        tis := tis.push (Syntax.getId A[1]!)
        tts := tts.push A[3]!
    | _ => throwError s!"Unexpected syntax at context {c}, expecting (x : T)"
  let os := os.getElems.raw
  liftTermElabM do
    elabAndLoadGTNode `g 0 {} gis gts <| fun gnodes c trans => do
      elabAndLoadUNode c trans uis uts uvs <| fun unodes _ trans => do
        elabAndLoadGTNode (.num `t 0) 0 trans tis tts <| fun tnodes _ trans => do
          let mut Os : Array Expr := #[]
          for o in os do
            let term ← elabTermAndSynthesize o .none
            let tterm := term.onAllSubtermsTR (fun
                | d@(.fvar fid) =>
                    match trans.find? fid.name with
                    | .none => d
                    | .some new => .fvar ⟨new⟩
                | x => x
                )
            Os := Os.push tterm
          IO.println "[Test] made it past loading of context and objects"
          let action ← evalConst (Array Expr → Array Expr → Array Expr → Array Expr → MetaM Unit) (metam.getId)
          action gnodes unodes tnodes Os


/-- 4.18, parser seems to have issue with ↓ gnodes and unodes in non-capital ...-/
def mkFakeDepCache (Gnodes Unodes : Array Expr) : MetaM (Array (List LocalDecl)) := do
  let total := Gnodes.size + Unodes.size
  let mut deps : Array (List LocalDecl) := Array.replicate total []
  for g in Gnodes ++ Unodes do
    let gd ← g.fvarId!.getDecl
    match gd with
    | .cdecl .. =>
        let T := gd.type
        let ds := T.getFVarIds
        for d in ds do
          match d.name with
          | .num _ j =>
              deps := deps.modify j (fun l => @List.insert _ ⟨fun x y => x.fvarId == y.fvarId⟩ gd l)
              -- Note that last additions are on top of the list, an assumptio we need for reverting with cutoffs
          | _ => continue
    | .ldecl _ _ _ T V .. =>
        let ds := T.getFVarIds ++ V.getFVarIds
        for d in ds do
          match d.name with
          | .num _ j =>
              deps := deps.modify j (fun l => @List.insert _ ⟨fun x y => x.fvarId == y.fvarId⟩  gd l)
              -- Note that last additions are on top of the list, an assumptio we need for reverting with cutoffs
          | _ => continue
  return deps


elab  "With" "gnodes" gs:("("ident ":" term")")*
      "and" "unodes" us:("("ident ":" term ":" term")")*
      "and" "tnodes" ts:("("ident ":" term")")*
      "and" "lnodes" ls:("("ident ":" term")")*
      "and" "objects" os:term,*
      "run" metam:ident : command => unsafe do
  let mut gts : Array Syntax := #[]
  let mut gis : Array Name := #[]
  for c in gs do
    match c.raw with
    | .node _ _ A =>
        gis := gis.push (Syntax.getId A[1]!)
        gts := gts.push A[3]!
    | _ => throwError s!"Unexpected syntax at context {c}, expecting (x : T)"
  let mut uts : Array Syntax := #[]
  let mut uvs : Array Syntax := #[]
  let mut uis : Array Name := #[]
  for c in us do
    match c.raw with
    | .node _ _ A =>
        uis := uis.push (Syntax.getId A[1]!)
        uts := uts.push A[3]!
        uvs := uvs.push A[5]!
    | _ => throwError s!"Unexpected syntax at context {c}, expecting (x : T : V)"
  let mut tts : Array Syntax := #[]
  let mut tis : Array Name := #[]
  for c in ts do
    match c.raw with
    | .node _ _ A =>
        tis := tis.push (Syntax.getId A[1]!)
        tts := tts.push A[3]!
    | _ => throwError s!"Unexpected syntax at context {c}, expecting (x : T)"
  let mut lts : Array Syntax := #[]
  let mut lis : Array Name := #[]
  for c in ls do
    match c.raw with
    | .node _ _ A =>
        lis := lis.push (Syntax.getId A[1]!)
        lts := lts.push A[3]!
    | _ => throwError s!"Unexpected syntax at context {c}, expecting (x : T)"
  let os := os.getElems.raw
  liftTermElabM do
    elabAndLoadGTNode `g 0 {} gis gts <| fun Gnodes c trans => do
      elabAndLoadUNode c trans uis uts uvs <| fun Unodes _ trans => do
        elabAndLoadGTNode (.num `t 0) 0 trans tis tts <| fun Tnodes _ trans => do
          elabAndLoadLNode (.num `dummyModule 0) 0 trans lis lts <| fun Lnodes _ trans => do
            let mut Os : Array Expr := #[]
            for o in os do
              let term ← elabTermAndSynthesize o .none
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
              Os := Os.push tterm
            IO.println "[Test] made it past loading of context and objects"
            let action ← evalConst (Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → MetaM Unit) (metam.getId)
            action Gnodes Unodes Tnodes Lnodes Os
