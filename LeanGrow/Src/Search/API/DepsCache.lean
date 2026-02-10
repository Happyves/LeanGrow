/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrowBeta.Search.Types

open Lean Meta

def updateDepsCaches (addedDecl : LocalDecl) (T : Expr) : GrowM Unit := do
  let ugIs := T.getGUFVarsIds.foldl (fun R fid => match fid with | ⟨.num _ i⟩ => i :: R | _ => R) []
  modify (fun st => {st with depsCache := (ugIs.foldl (fun R i => R.modify i (fun y => addedDecl :: y)) st.depsCache).push []})


def updateDepsCachesPreComp (addedDecl : LocalDecl) (ugIs : List Nat) : GrowM Unit := do
  modify (fun st => {st with depsCache := (ugIs.foldl (fun R i => R.modify i (fun y => addedDecl :: y)) st.depsCache).push []})


def updateDepsCachesPreCompNoMonad (addedDecl : LocalDecl) (ugIs : List Nat)
  (st : SearchState (List Nat)) : (SearchState (List Nat)) :=
  {st with depsCache := (ugIs.foldl (fun R i => R.modify i (fun y => addedDecl :: y)) st.depsCache).push []}
