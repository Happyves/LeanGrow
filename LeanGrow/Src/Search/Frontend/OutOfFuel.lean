
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Search.Frontend.Initialize

open Lean Meta Elab Tactic


#check 1

def getRelevantForwIds (g : Expr) (IT : IntroTree UInt32Array) : UInt32Array :=
  match g with
  | .forallE .. | .letE .. =>
    match IT with
    | .node _ _ _ _ _ kids =>
      match kids with
      | .cons _ _ main _  =>
          match main with
          | .node _ is  .. => is
          | .leaf _ is .. => is
      | _ => .empty
    | _ => .empty
  | _ => .empty




def growOutOfFuel (msgRef : Syntax) (g : Expr) (st : SearchState UInt32Array) : MetaM Unit :=
  do
  mtracing
  let mut msg := "[Grow] ran out of fuel without finding solution. Printing forward steps:\n\n"
  let relevant := getRelevantForwIds g st.introTree
  let relevant := relevant.foldl [] (fun i L => i.toNat :: L)
  mtrace on .zero with s!"[growOutOfFuel] relevant {relevant}"
  mtrace on .zero with s!"[growOutOfFuel] introTree {st.introTree.pp 0}"
  for i in relevant do
    let ug := if st.uNodes.binSearchContains i (· < ·) then unode i else gnode i
    match ← (⟨ug⟩ : FVarId).getDecl with
    | .cdecl _ _ name type .. =>
      msg := msg ++ s!"   {name} : {← ppExpr type}\n\n"
    | .ldecl _ _ name type val .. =>
      msg := msg ++ s!"   {name} : {← ppExpr type}\n   Term : {← ppExpr val}\n\n"
  logWarningAt msgRef msg
