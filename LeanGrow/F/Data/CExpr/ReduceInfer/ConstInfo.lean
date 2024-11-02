
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

instance : BEq InductiveVal where
  beq := fun ⟨a,b,c,d,e,f,g,h,i⟩ ⟨A,B,C,D,E,F,G,H,I⟩ =>
    (a == A) && (b == B) && (c == C) && (d == D) && (e == E) && (f == F) && (g == G) && (h == H) && (i == I)


instance : Repr InductiveVal where
  reprPrec := fun ⟨_,b,c,d,e,f,g,h,i⟩ _ =>
    "{" ++ s!"numParams := {repr b}, numIndices := {repr c}, all := {repr d}, ctors := {repr e}, isRec := {repr f}, isUnsafe := {repr g}, isReflexive := {repr h}, isNested := {repr i}" ++ "}"


instance : BEq ConstructorVal where
  beq := fun ⟨a,b,c,d,e,f⟩ ⟨A,B,C,D,E,F⟩ =>
    (a == A) && (b == B) && (c == C) && (d == D) && (e == E) && (f == F)


instance : Repr ConstructorVal where
  reprPrec := fun ⟨_,b,c,d,e,f⟩ _ =>
    "{" ++ s!"induct := {repr b}, cidx := {repr c}, numParams := {repr d}, numFields := {repr e}, isUnsafe := {repr f}" ++ "}"


inductive CstInfo where
| wVal (levelParams : List Lean.Name) (type : CExpr) (val : CExpr)
| noVal (levelParams : List Lean.Name) (type : CExpr)
| struc (levelParams : List Lean.Name) (type : CExpr) (ctorName : Lean.Name) (ctorVal : ConstructorVal)
| mat (levelParams : List Lean.Name) (type : CExpr) (val : CExpr) (info : MatcherInfo)
| indu (levelParams : List Lean.Name) (type : CExpr) (info : InductiveVal)
deriving Inhabited, BEq, Repr

def CstInfo.type : CstInfo → CExpr
  | .wVal _ t _ => t
  | .noVal _ t => t
  | .struc _ t _ _=> t
  | .mat _ t _ _ => t
  | .indu _ t _ => t

def CstInfo.levelParams : CstInfo → List Lean.Name
  | .wVal t _ _ => t
  | .noVal t _ => t
  | .struc t _ _ _ => t
  | .mat t _ _ _ => t
  | .indu t _ _ => t


/-
Notes:

- Don't forget to recognize structures when building the Trie (via !isStructureLike ?)
- also get rid of annotations to account for Expr.consumeTypeAnnotations (in inferProj)


-/
