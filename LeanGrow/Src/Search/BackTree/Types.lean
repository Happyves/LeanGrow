
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Lean.Meta.Basic
import LeanGrowBeta.Data.Amalgames
import LeanGrowBeta.Utils.Std.String

open Lean Meta

inductive BackStepMetadata where
| none
| string (msg : String)
| std (thmName : String)
| recu (thmName : String)
deriving Inhabited, BEq, Repr

/-- Ids are assumed to be sorted-/
inductive BackTree where
| fail (msg : String)
| ofUni (pass : Nat) (uni_ids : List Nat) (value : Expr)
| ofPropa (pass : Nat) (uni_ids : List Nat) (goal_id : Nat) (newType : Expr) (bdirs : (List Nat)) (gdirs : (List Nat)) (args : List BackTree)
| ofGoal (pass goal_id : Nat) (type : Expr) (bdirs : (List Nat)) (gdirs : (List Nat)) (args : List BackTree)
| ofBack (pass back_id : Nat) (mdata : BackStepMetadata) (thm : Expr) (bdirs : Array (List Nat)) (gdirs : Array (List Nat)) (args : Array BackTree)
| ofIntro (pass back_id : Nat) (gnIdxAndTy : ListProd FVarId Expr) (bdirs : (List Nat)) (gdirs : (List Nat)) (args : List BackTree)
deriving Inhabited, BEq, Repr


def BackStepMetadata.pp : BackStepMetadata → MetaM String
| .none => return ""
| .string s | .std s | .recu s => return s


partial def BackTree.pp (ind : Nat) : BackTree → MetaM String
| .fail s => return (Blank ind) ++ s!"fail {s}"
| .ofUni pass (uniId : List Nat) (value : Expr) =>
    return (Blank ind) ++ s!"ofU ({pass}) ({uniId}) {← ppExpr value}"
| .ofPropa pass u g (newtype : Expr) _ _ (args : List BackTree) =>
    return (Blank ind) ++s!"ofP ({pass}) ({u}) ({g}) {← ppExpr newtype}\n" ++ (← BlankJumpM (ind +3) args (BackTree.pp (ind + 3)))
| .ofGoal pass (g : Nat) (type : Expr) _ _ (args : List BackTree) =>
    return (Blank ind) ++ s!"ofG ({pass}) ({g}) {← ppExpr type}\n" ++ (← BlankJumpM (ind +3) args (BackTree.pp (ind + 3)))
| .ofBack pass (g : Nat) (mdata : BackStepMetadata) _ _ _ (args : Array BackTree) =>
    return (Blank ind) ++ s!"ofB ({pass}) ({g}) {← mdata.pp}\n" ++ (← BlankJumpM (ind +3) args.toList (BackTree.pp (ind + 3)))
| .ofIntro pass (gid : Nat) (gnIdxAndTy : ListProd FVarId Expr) _ _ (args : List BackTree) =>
    return (Blank ind) ++ s!"ofI ({pass}) ({gid}) ({← gnIdxAndTy.toListOfProd.mapM (fun x => ppExpr x.2)})\n" ++ (← BlankJumpM (ind +3) args (BackTree.pp (ind + 3)))


partial def BackTree.ppDirs (ind : Nat) : BackTree → String
| .fail s => (Blank ind) ++ s!"fail {s}"
| .ofUni pass (uniId : List Nat) _ =>
    (Blank ind) ++ s!"ofU ({pass}) ({uniId})"
| .ofPropa pass u g _ bd gd (args : List BackTree) =>
    (Blank ind) ++s!"ofP ({pass}) ({u}) ({g}) ({bd}) ({gd})\n" ++ (BlankJump (ind +3) args (BackTree.ppDirs (ind + 3)))
| .ofGoal pass (g : Nat) _ bd gd (args : List BackTree) =>
    (Blank ind) ++ s!"ofG ({pass}) ({g}) ({bd}) ({gd})\n" ++ (BlankJump (ind +3) args (BackTree.ppDirs (ind + 3)))
| .ofBack pass (g : Nat) _ _ bd gd (args : Array BackTree) =>
    (Blank ind) ++ s!"ofB ({pass}) ({g}) ({bd}) ({gd})\n" ++ (BlankJump (ind +3) args.toList (BackTree.ppDirs (ind + 3)))
| .ofIntro pass (gid : Nat) _ bd gd (args : List BackTree) =>
    (Blank ind) ++ s!"ofI ({pass}) ({gid}) ({bd}) ({gd})\n" ++ (BlankJump (ind +3) args (BackTree.ppDirs (ind + 3)))
