
import LeanGrow.F.Data.CExpr.Types
import Lean.Meta.Match.MatcherInfo

open Lean Meta Match

instance : BEq DiscrInfo where
  beq := fun ⟨a⟩ ⟨b⟩ => a == b

instance : Repr DiscrInfo where
  reprPrec := fun ⟨a⟩ n => reprPrec a n


instance : BEq MatcherInfo where
  beq := fun ⟨a,b,c,d,e⟩ ⟨A,B,C,D,E⟩ =>
    (a == A) && (b == B) && (c == C) && (d == D) && (e == E)


instance : Repr MatcherInfo where
  reprPrec := fun ⟨a,b,c,d,e⟩ _ =>
    "{" ++ s!"numParams := {repr a}, numDiscrs := {repr b}, altNumParams := {repr c}, uElimPos? := {repr d}, discrInfos := {repr e}" ++ "}"

inductive CstInfo where
| wVal (levelParams : List Lean.Name) (type : CExpr) (val : CExpr)
| noVal (levelParams : List Lean.Name) (type : CExpr)
| struc (levelParams : List Lean.Name) (type : CExpr) (ctorName : Lean.Name)
| mat (levelParams : List Lean.Name) (type : CExpr) (val : CExpr) (info : MatcherInfo)
deriving Inhabited, BEq, Repr

def CstInfo.type : CstInfo → CExpr
  | .wVal _ t _ => t
  | .noVal _ t => t
  | .struc _ t _ => t
  | .mat _ t _ _ => t

def CstInfo.levelParams : CstInfo → List Lean.Name
  | .wVal t _ _ => t
  | .noVal t _ => t
  | .struc t _ _ => t
  | .mat t _ _ _ => t


/-
Notes:

- Don't forget to recognize structures when building the Trie
- also get rid of annotations to account for Expr.consumeTypeAnnotations (in inferProj)


-/
