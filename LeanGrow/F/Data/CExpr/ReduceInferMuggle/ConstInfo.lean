
import LeanGrow.F.Data.CExpr.API
import Lean.Meta.Match.MatcherInfo
import Lean.Structure

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


#check RecursorVal

structure cRecursorRule where
  ctor : Name
  nfields : Nat
  rhs : CExpr
deriving Inhabited, BEq, Repr

def RecursorRule.tocRecursorRule : RecursorRule → cRecursorRule
| .mk c n rhs => .mk c n rhs.toCExprF



structure cRecursorVal where
  all : List Name
  numParams : Nat
  numIndices : Nat
  numMotives : Nat
  numMinors : Nat
  rules : List cRecursorRule
  k : Bool
  isUnsafe : Bool
deriving Inhabited, BEq


def RecursorVal.tocRecursorVal : RecursorVal → cRecursorVal
| .mk _ a b c d e R f g => .mk a b c d e (R.map RecursorRule.tocRecursorRule) f g


instance : Repr cRecursorVal where
  reprPrec := fun ⟨a,b,c,d,e,f,g,h⟩ _ =>
    "{" ++ s!"all := {a}, numParams := {repr b}, numIndices := {repr c}, numMotives := {repr d}, numMinors := {repr e}, rules := {repr f}, k := {repr g}, isUnsafe := {repr h}" ++ "}"


instance : BEq QuotKind where
  beq := fun a b =>
    match a, b with
    | .type, .type => true
    | .ctor, .ctor => true
    | .lift, .lift => true
    | .ind, .ind => true
    | _, _ => false


instance : Repr QuotKind where
  reprPrec := fun b _ =>
    match  b with
    | .type => "type"
    | .ctor => "ctor"
    | .lift => "lift"
    | .ind => "ind"

instance : BEq QuotVal where
  beq := fun ⟨a,b⟩ ⟨A,B⟩ => (a == A) && (b == B)

instance : Repr QuotVal where
  reprPrec := fun ⟨_,b⟩ _ => repr b




inductive CstInfo where
| wVal (levelParams : List Lean.Name) (type : CExpr) (val : CExpr)
| noVal (levelParams : List Lean.Name) (type : CExpr)
| struc (levelParams : List Lean.Name) (type : CExpr) (ctorName : Lean.Name) (ctorVal : ConstructorVal)
| mat (levelParams : List Lean.Name) (type : CExpr) (val : CExpr) (info : MatcherInfo)
| indu (levelParams : List Lean.Name) (type : CExpr) (info : InductiveVal)
| recu (levelParams : List Lean.Name) (type : CExpr) (info : cRecursorVal)
| quot (levelParams : List Lean.Name) (type : CExpr) (info : QuotVal)
| ctor (levelParams : List Lean.Name) (type : CExpr) (info : ConstructorVal)
deriving Inhabited, BEq, Repr

def CstInfo.type : CstInfo → CExpr
  | .wVal _ t _ => t
  | .noVal _ t => t
  | .struc _ t _ _=> t
  | .mat _ t _ _ => t
  | .indu _ t _ => t
  | .recu _ t _ => t
  | .quot _ t _ => t
  | .ctor _ t _ => t


def CstInfo.levelParams : CstInfo → List Lean.Name
  | .wVal t _ _ => t
  | .noVal t _ => t
  | .struc t _ _ _ => t
  | .mat t _ _ _ => t
  | .indu t _ _ => t
  | .recu t _ _ => t
  | .quot t _ _ => t
  | .ctor t _ _ => t



def isStructureLike! (env : Environment) (constName : Name) : Option (Name × ConstructorVal) :=
  match env.find? constName with
  | some (.inductInfo { isRec := false, ctors := [C], numIndices := 0, .. }) =>
        match env.find? C with
        | some (.ctorInfo V) => .some (C,V)
        | _ => .none
  | _ => .none

def ConstantInfo.toCstInfo (env : Environment) (n : Name) (i : ConstantInfo) : CstInfo :=
  let rec main :  ConstantInfo → CstInfo
    | .axiomInfo v => .noVal v.levelParams v.type.toCExprF
    | .defnInfo v | .thmInfo v | .opaqueInfo v => .wVal v.levelParams v.type.toCExprF v.value.toCExprF
    | .quotInfo v => .quot v.levelParams v.type.toCExprF v
    | .inductInfo v => .indu v.levelParams v.type.toCExprF v
    | .ctorInfo v => .ctor v.levelParams v.type.toCExprF v
    | .recInfo v => .recu v.levelParams v.type.toCExprF (RecursorVal.tocRecursorVal v)
  match isStructureLike! env n with
  | .some (c,v) => .struc i.levelParams i.type.toCExprF c v
  | .none =>
      match Lean.Meta.getMatcherInfoCore? env n with
      | .some mi => .mat i.levelParams i.type.toCExprF i.value!.toCExprF mi
      | .none => main i
