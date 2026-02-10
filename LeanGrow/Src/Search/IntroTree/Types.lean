
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrowBeta.Data.PathIndex.Types
import LeanGrowBeta.Utils.Std.String

open Lean Meta

variable {IndexColType : Type}

/-- Ids are assumed to be sorted-/
inductive IntroTree (IndexColType : Type) where
| leaf (goalIds guIds : List Nat) (goalP ltx : PaIn IndexColType)
| node (goalIds guIds : List Nat) (goalP ltx : PaIn IndexColType) (kidsWdirs : ListProd3 IndexColType IndexColType (IntroTree IndexColType))
deriving Inhabited, Repr


partial def IntroTree.pp (ind : Nat) : IntroTree IndexColType → String
  | .leaf goalIds guIds .. =>
      (Blank ind) ++ s!"leaf {goalIds} {guIds}"
  | .node goalIds guIds _ _ kids =>
      let args := kids.foldl [] (fun _ _ it R => it :: R)
      (Blank ind) ++s!"node {goalIds} {guIds}\n" ++ (BlankJump (ind +3) args (IntroTree.pp (ind + 3)))



partial def IntroTree.ppDirs [Repr IndexColType] (ind : Nat) : IntroTree IndexColType → String
  | .leaf goalIds guIds .. =>
      (Blank ind) ++ s!"leaf {goalIds} {guIds}"
  | .node goalIds guIds _ _ kids =>
      let args := kids.toListOfProd
      (Blank ind) ++ s!"node {goalIds} {guIds}\n" ++ (BlankJump (ind +3) args (fun (gD, fD, kid) => (Blank (ind+3)) ++ s!"node {repr gD} {repr fD}\n" ++ (kid.ppDirs (ind + 3))))
