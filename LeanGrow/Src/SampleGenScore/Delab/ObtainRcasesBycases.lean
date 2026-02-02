
/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.SampleGenScore.Delab.InductionCases

open Lean Meta

#eval isInductionCasesStuff `Quot.ind
#check Quot.ind


/- Expects app, but will headBeta, so we keep it unprocessed-/
@[inline]
partial def delabSample_ObtRCaseIndCase_core (e : Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (Prod3 (Option (List Expr)) LocalContext LocalInstances) := do
  let core (e : Expr) := do
    let e := e.headBeta
    let appH := e.getAppFn'
    let .const h _ := appH | return .mk .none l1 l2
    if h == ``Quot.ind
    then
      let appA := e.getAppArgs
      let funin ← withLCtx l1 l2 <| getFunInfo appH
      let fa := funin.getArity
      let main := mkAppN appH (appA.take fa)
      let rarg ← main.withRelevantArgsBack l1 l2 (appA.drop fa) [] (fun a L => return a :: L)
      return .mk (.some rarg) l1 l2
    else
      if h == ``Eq.casesOn
      then
        lambdaTelescope (e.getArg! 5) <| fun _ b => do
          let h := b.getAppFn'
          let as := b.getAppArgs
          let R ← delabSample_Acyclic_core h as
          match R with
          | .none => return .mk .none l1 l2
          | .some _ => return .mk (.some []) l1 l2
      else
        if ← isInductionCasesStuff h
        then
          let appA := e.getAppArgs
          let _ ← realizeGlobalConstNoOverloadCore h
          let funin ← withLCtx l1 l2 <| getFunInfo appH
          let fa := funin.getArity
          let main := mkAppN appH (appA.take fa)
          let rarg ← main.withRelevantArgsBack l1 l2 (appA.drop fa) [] (fun a L => return a :: L)
          let rarg := rarg.filter (fun -- happens in casesOn ; adds a `fv = cons` to motive ...
            | .app (.app (.const h _) _) (.fvar _) => if h == `Eq.refl then false else true
            | _ => true
            )
          return .mk (.some rarg) l1 l2
        else
          return .mk .none l1 l2
  match e.getAppFn' with
  | .const h _ =>
    if h == ``dite
    then
      return .mk (.some []) l1 l2
    else
      core e
  | _ =>
    core e


@[inline]
partial def delabDig_ObtRCaseIndCase_core (e : Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (Prod3 (Option (List Expr)) LocalContext LocalInstances) := do
  let core (e : Expr) := do
    let e := e.headBeta
    let appH := e.getAppFn'
    let .const h _ := appH | return .mk .none l1 l2
    if h == ``Quot.ind
    then
      let appA := e.getAppArgs
      let funin ← withLCtx l1 l2 <| getFunInfo appH
      let fa := funin.getArity
      let main := mkAppN appH (appA.take fa)
      let reverts ← main.withRelevantArgsBack l1 l2 (appA.drop fa) [] (fun a L => return a :: L)
      return .mk (.some (appA[3]! :: reverts)) l1 l2
    else
      if h == ``Eq.casesOn
      then
        lambdaTelescope (e.getArg! 5) <| fun _ b => do
          let h := b.getAppFn'
          let as := b.getAppArgs
          let R ← delabSample_Acyclic_core h as
          match R with
          | .none => return .mk .none l1 l2
          | .some _ => return .mk (.some []) l1 l2
      else
        if ← isInductionCasesStuff h
        then
          let appA := e.getAppArgs
          let _ ← realizeGlobalConstNoOverloadCore h
          let funin ← withLCtx l1 l2 <| getFunInfo appH
          let fa := funin.getArity
          let main := mkAppN appH (appA.take fa)
          let reverts ← main.withRelevantArgsBack l1 l2 (appA.drop fa) [] (fun a L => return a :: L)
          let reverts := reverts.filter (fun -- happens in casesOn ; adds a `fv = cons` to motive ...
            | .app (.app (.const h _) _) (.fvar _) => if h == `Eq.refl then false else true
            | _ => true
            )
          let info ← getElimInfo h
          let poses ← getElimSubproofsPos info
          let indPrfs := poses.foldl (fun L i => appA[i]! :: L) []
          return .mk (.some (indPrfs ++ reverts)) l1 l2
        else
          return .mk .none l1 l2
  match e.getAppFn' with
  | .const h _ =>
    if h == ``dite
    then
      let as := e.getAppArgs
      return .mk (.some [as[3]!, as[4]!]) l1 l2
    else
      core e
  | _ =>
    core e



@[inline]
partial def delabSample_ObtRCaseIndCase_topBack (e : Expr)
  : MetaM SampleData := do
  let core (e : Expr) := do
    let e := e.headBeta
    let appH := e.getAppFn'
    let .const h _ := appH | return .none
    if h == ``Quot.ind
    then
      return .induc h
    else
      if ← isInductionCasesStuff h
      then
        return .induc h
      else
        return .none
  match e with
  | .app (.lam _ T _ _) D =>
      match D with
      | .app (.const cem? _) p? =>
        if cem? == ``Classical.em then return (.thmC ``Classical.byCases #[p?]) else core e
      | _ =>
        match T with
        | .app (.const dec? _) p? =>
          if dec? == ``Decidable then return (.thmC ``Classical.byCases #[p?]) else core e
        | _ =>
          core e
  | _ =>
    match e.getAppFn' with
    | .const h _ =>
      if h == ``dite then return (.thmC ``Classical.byCases #[(e.getArg! 1)])else core e
    | _ => core e



@[inline]
partial def delabSample_ObtRCaseIndCase_topForw (e : Expr)
  : MetaM Bool := do
  let core (e : Expr) := do
    let e := e.headBeta
    let appH := e.getAppFn'
    let .const h _ := appH | return false
    if h == ``Quot.ind
    then
      return true
    else
      if ← isInductionCasesStuff h
      then
        return true
      else
        return false
  match e with
  | .app (.lam _ T _ _) D =>
      match D with
      | .app (.const cem? _) _ =>
        if cem? == ``Classical.em then return true else core e
      | _ =>
        match T with
        | .app (.const dec? _) _ =>
          if dec? == ``Decidable then return true else core e
        | _ =>
          core e
  | _ =>
    match e.getAppFn' with
    | .const h _ =>
      if h == ``dite then return true else core e
    | _ => core e
