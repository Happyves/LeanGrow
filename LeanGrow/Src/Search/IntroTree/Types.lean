
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Data.PathIndexG.Types
import LeanGrow.Src.Utils.Std.String

open Lean Meta

variable {IndexColType : Type}

/-- Ids are assumed to be sorted-/
inductive IntroTree (IndexColType : Type) where
| leaf (l2 : LocalInstances) (goalIds guIds : IndexColType) (goalP ltx : PaInG IndexColType)
| node (l2 : LocalInstances) (goalIds guIds : IndexColType) (goalP ltx : PaInG IndexColType)
    (kidsWdirs : ListProd3 IndexColType IndexColType (IntroTree IndexColType))
deriving Inhabited


partial def IntroTree.pp [Repr IndexColType] (ind : Nat) : IntroTree IndexColType → String
  | .leaf _ goalIds guIds .. =>
      (Blank ind) ++ s!"leaf {repr goalIds} {repr guIds}"
  | .node _ goalIds guIds _ _ kids =>
      let args := kids.foldl [] (fun _ _ it R => it :: R)
      (Blank ind) ++s!"node {repr goalIds} {repr guIds}\n" ++ (BlankJump (ind +3) args (IntroTree.pp (ind + 3)))



partial def IntroTree.ppDirsLocInst [Repr IndexColType] (ind : Nat) : IntroTree IndexColType → String
  | .leaf l2 goalIds guIds .. =>
      (Blank ind) ++ s!"leaf {l2.map LocalInstance.fvar} {repr goalIds} {repr guIds}"
  | .node l2 goalIds guIds _ _ kids =>
      let args := kids.toListOfProd
      (Blank ind) ++ s!"node {l2.map LocalInstance.fvar} {repr goalIds} {repr guIds}\n" ++ (BlankJump (ind +3) args (fun (gD, fD, kid) => (Blank (ind+3)) ++ s!"node {repr gD} {repr fD}\n" ++ (kid.ppDirsLocInst (ind + 3))))
