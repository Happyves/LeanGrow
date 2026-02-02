

/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Lean.Meta.Basic
import LeanGrow.Src.Data.Amalgames
import LeanGrow.Src.Utils.Lean.MetaAPI

open Lean Meta


inductive SubProof where
| raw (_ : Expr)
| irreducible (_ : Expr)
| simp (_ : ListProd3 (List FVarId) Expr Expr) (_ : Option Expr) (usedFv : List FVarId)
deriving Inhabited, Repr


def SubProof.pp (l1 : LocalContext) (l2 : LocalInstances) : SubProof → MetaM String
  | .raw e => return s!"(raw) {← PpExpr e l1 l2}"
  | .irreducible e => return s!"(irred) {← PpExpr e l1 l2}"
  | .simp l _ _ => return s!"(simp) {← l.foldlM "" (fun _ a b R => return R ++ s!"{← PpExpr a l1 l2} {← PpExpr b l1 l2}")}"


inductive SampleData where
| none
| thm (n : Name)
| induc (n : Name)
| thmC (n : Name) (cs : Array Expr)
deriving Inhabited, Repr, BEq


def SampleData.pp : SampleData → MetaM String
  | none => return "none"
  | thm (n : Name) => return s!"thm {n}"
  | induc (n : Name) => return s!"induc {n}"
  | thmC (n : Name) (cs : Array Expr) => return s!"thmC {n} {← cs.mapM ppExpr}"
