/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.SampleGenScore.Utils

open Lean Meta



def Lean.Expr.headBetaLet (e : Expr) : Expr :=
  let f := e.getAppFn
  if f.isHeadBetaTargetFn true then betaRev f e.getAppRevArgs true true else e

#check Expr.headBeta

@[inline]
def substArgIrrelevant (l1 : LocalContext) (l2 : LocalInstances) (e : Expr) : MetaM (Option Expr) :=
  let h := e.getAppFn'
  match h with
  | .const h _ =>
    if h == ``Eq.symm
    then
      match (e.getArg! 3)  with
      | x@(.fvar fvid) => do
          match ← fvid.GetDecl l1 l2 with
          | .ldecl .. => return .some x
          | _ => return .none
      | x => if x.isAtomic then return .none else return .some x
    else
      if h == ``eq_of_heq
      then
        match (e.getArg! 3)  with
        | x@(.fvar fvid) => do
            match ← fvid.GetDecl l1 l2 with
            | .ldecl .. => return .some x
            | _ => return .none
        | x => if x.isAtomic then return .none else return .some x
      else
        return .none
  | _ => return .none



@[inline]
partial def delabSample_subst_core (appH : Expr) (appA : Array Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (Prod3 (Option (List Expr)) LocalContext LocalInstances) := do
  mtracing
  let rec getCore (h : Expr) (as : Array Expr) (res : List Expr) : MetaM (Prod3 Expr (Array Expr) (List Expr)) :=
    match h with
    | .lam .. | .letE .. | .mdata .. => do
      let ne := Expr.betaRev h as.reverse true true
      let nea := ne.getAppArgs
      let res ← nea.foldlM (fun L a => do
        match ← substArgIrrelevant l1 l2 a with
        | .none => return L
        | .some a => return a :: L
        ) res
      getCore ne.getAppFn nea res
    | _ => return .mk h as res
  mtrace on .zero with s!" inital appH : {← PpExpr appH l1 l2}\n appA : {← appA.mapM (PpExpr · l1 l2)}"
  let .mk h as res ← getCore appH appA []
  mtrace on .zero with s!" post getCore appH : {← PpExpr appH l1 l2}\n appA : {← appA.mapM (PpExpr · l1 l2)}"
  match h with
  | .const h _ =>
      if h == ``Eq.rec || h == ``Eq.ndrec
      then
        mtrace on .zero with s!" success, proceed with Term :\n{← PpExpr as[3]! l1 l2}\nType :\n{← PpExpr (← InferType as[3]! l1 l2) l1 l2}"
        match as[5]! with
        | .fvar .. =>
          return .mk (as[3]! :: res) l1 l2
        | A =>
          match A.getAppFn' with
          | .const n _ =>
            if n == ``Eq.symm
            then return .mk ((A.getArg! 3) :: as[3]! :: res) l1 l2
            else return .mk (A :: as[3]! :: res) l1 l2
          | _ => return .mk (A :: as[3]! :: res) l1 l2
      else
        return .mk .none l1 l2
        -- ↑ ↓ wasnÄt subst, try other delab
  | _ => return .mk .none l1 l2




#check Eq.rec
#check Eq.ndrec



#check Eq.symm
#check eq_of_heq
