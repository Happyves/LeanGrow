

/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.SampleGenScore.Delab.Subst
import LeanGrow.Src.SampleGenScore.Delab.InjNoConfAcyclic

open Lean Meta



@[inline]
def isElabElims (n : Name) : MetaM Bool := do
  let env ← getEnv
  let ext := (TagAttribute.ext Lean.Elab.Term.elabAsElim).getState env
  return ext.contains n


@[inline]
def isCustomElims (n : Name) : MetaM Bool := do
  let env ← getEnv
  let elims := customEliminatorExt.getState env |>.map
  for (_,val) in elims do
    if n == val then return true
  return false


@[inline]
def isInductionCasesStuff (n : Name) : MetaM Bool := do
  match n with
  | .str h suff =>
    if h != ``Eq
    then
      match suff with
      | "rec" | "casesOn" | "recAux" | "casesAuxOn" | "induct" | "induct_unfolding" | "mutual_induct" | "mutual_induct_unfolding" | "fun_cases" | "fun_cases_unfolding" =>
        return true
      | _ =>
        if ← isElabElims n then return true else (if ← isCustomElims n then return true else return false)
    else
      if ← isElabElims n then return true else (if ← isCustomElims n then return true else return false)
  | _ =>
      if ← isElabElims n then return true else (if ← isCustomElims n then return true else return false)



/- Expects app, but will headBeta, so we keep it unprocessed-/
@[inline]
partial def delabSample_InductionCases_core (e : Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (Prod4 (List FVarId) (Option (List Expr)) LocalContext LocalInstances) := do
  let e := e.headBeta
  let appH := e.getAppFn'
  let .const h _ := appH | return .mk [] .none l1 l2
  if ← isInductionCasesStuff h
  then
    let appA := e.getAppArgs
    let funin ← withLCtx l1 l2 <| getFunInfo appH
    let main := mkAppN appH (appA.take funin.getArity)
    let rarg ← main.withRelevantArgsBack l1 l2 appA [] (fun a L => return a :: L)
    return .mk [] (.some rarg) l1 l2
  else
    return .mk [] .none l1 l2


#check 1



def getElimSubproofsPos (info : ElimInfo) : MetaM (Array Nat) := do
  forallTelescopeReducing info.elimType fun xs _ => do
    let mut res := #[]
    for h : i in *...xs.size do
      let x := xs[i]
      let xDecl ← x.fvarId!.getDecl
      if xDecl.binderInfo.isExplicit then
        let name := xDecl.userName
        match info.altsInfo.find? (fun x => x.name == name) with
        | .some a =>
            if a.provesMotive then
              res := res.push i
        | _ => continue
    return res



@[inline]
partial def delabDig_InductionCases_core (e : Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (Prod4 (List FVarId) (Option (List Expr)) LocalContext LocalInstances) := do
  let e := e.headBeta
  let appH := e.getAppFn'
  let .const h _ := appH | return .mk [] .none l1 l2
  if ← isInductionCasesStuff h
  then
    let appA := e.getAppArgs
    let funin ← withLCtx l1 l2 <| getFunInfo appH
    let main := mkAppN appH (appA.take funin.getArity)
    let reverts ← main.withRelevantArgsBack l1 l2 appA [] (fun a L => return a :: L)
    let _ ← realizeGlobalConstNoOverloadCore h
    let info ← getElimInfo h
    let poses ← getElimSubproofsPos info
    let indPrfs := poses.foldl (fun L i => appA[i]! :: L) []
    return .mk [] (.some (indPrfs ++ reverts)) l1 l2
  else
    return .mk [] .none l1 l2


@[inline]
partial def delabSample_InductionCases_topBack (e : Expr)
  : MetaM (Option SampleData) := do
  let e := e.headBeta
  let appH := e.getAppFn'
  let .const h _ := appH | return .none
  if ← isInductionCasesStuff h
  then
    return .some <| .induc h
  else
    return .none
