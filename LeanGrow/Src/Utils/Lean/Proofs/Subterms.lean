
/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Utils.Tracing
import LeanGrow.Src.Utils.Lean.LocalContext
import LeanGrow.Src.Utils.Lean.Expr.Fail
import LeanGrow.Src.Utils.LeanGrow.Nodes

open Lean Meta


def mkValLikeCore (n : Name) : MetaM Unit := do
  let env ← getEnv
  let .some info := (env.find? n) | throwError s!"{n} unknown"
  let .some val := info.value? | throwError s!"{n} has no value"
  let N := Name.str n "like"
  let eq ← mkEq (.const n (info.levelParams.map .param)) val
  let dec : Declaration := .defnDecl <| {
    name := N
    levelParams := info.levelParams
    type := .sort 0
    value := eq
    hints := .regular 0
    safety := .safe
  }
  addDecl dec

elab "add_valLike" n:ident : command => do
  let N := n.getId
  Elab.Command.liftTermElabM (mkValLikeCore N)

elab "ppElabOf" t:term : term => do
  let t ← Elab.Term.elabTermAndSynthesize t .none
  logInfoAt (← getRef) ( t)
  return t

#check 1


@[specialize f, inline]
partial def Lean.Expr.onAllSubtermsWiDepth (e : Expr) (f : Expr → Nat → Expr) : Expr :=
  -- caching here is bad idea because cached term can appear in different depths,
  -- and bvar indices will be wrong there. This happend.
  let rec @[specialize f] go (e : Expr) (d : Nat) : Expr :=
    match f e d with
    | .app l r =>
      let l := go l d
      let r := go r d
      .app l r
    | .lam n l r bi =>
      let l := go l d
      let r := go r (d+1)
      .lam n l r bi
    | .forallE n l r bi =>
      let l := go l d
      let r := go r (d+1)
      .forallE n l r bi
    | .letE n l r z bi =>
      let l := go l d
      let r := go r d
      let z := go z (d+1)
      .letE n l r z bi
    | .proj n i l =>
      let l := go l d
      .proj n i l
    | .mdata da l =>
      let l := go l d
      .mdata da l
    | t => t
  go e 0

open Elab Term


def help : Expr → TermElabM FVarId
  | .mdata _ e => help e
  | .fvar i => return i
  | _ => throwError "bad format"

@[specialize f,inline]
partial def Lean.Level.onAllSubtermsFold (e : Level)
  {α : Sort _} (init : α) (f : Level → α → α) : α :=
  let rec @[specialize f] go (col : α) : Level → α
    | e  =>
      let here := f e col
      match e with
      | .max l r | .imax l r => let nx := go here l ; go nx r
      | .succ e => go (here) e
      | _ => here
  go init e

def mkValLikeCore' (fu body : Expr) : TermElabM Unit := do
  let fv ← help fu
  let N ← fv.getUserName
  let N := Name.str N "like"
  let (_,allFv) ←  body.collectFVars.run {}
  let absed := body.abstract (allFv.fvarIds.map Expr.fvar) -- ignores dependencies
  -- bindddmfnrjngqöejn
  let T ← inferType fu
  let lv ← getLevel T
  let eq := mkAppN (.const ``Eq [lv]) #[T,(.bvar 0), absed]
  let lvl := lv.onAllSubtermsFold [] (fun | .param n, s => s.insert n | _,s => s) -- not in right order ...
  let eq := Expr.lam `f T eq .default
  let dec : Declaration := .defnDecl <| {
    name := N
    levelParams := lvl
    type := .sort 0
    value := eq
    hints := .regular 0
    safety := .safe
  }
  addDecl dec


elab "add_valLike_of" fu:term "in" body:term : term => do
  let fu ← Elab.Term.elabTermAndSynthesize fu .none
  let body ← Elab.Term.elabTermAndSynthesize body .none
  mkValLikeCore' fu body
  return body


#check Meta.getLevel

#exit

@[specialize f]
partial def Lean.Expr.onAllSubterms (e : Expr) (f : Expr → Expr) : Expr :=
  let rec @[specialize f] go (e : Expr) : Expr :=
    -- ppElabOf
    add_valLike_of go in
    let here := f e
    match here with
    | .app l r => Expr.app (go l) (go r)
    | .lam n l r i => .lam n (go l) (go r)  i
    | .forallE n l r i => .forallE n (go l) (go r)  i
    | .letE n l r z i => .letE n (go l) (go r) (go z)  i
    | .proj n i e => .proj n i (go e)
    | .mdata d e => .mdata d (go e)
    | _ => here
  go e

-- add_valLike Lean.Expr.onAllSubterms.go
-- has no val you dummy

#check 1
