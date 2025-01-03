
import LeanGrow.F.Data.CExpr.Types
import LeanGrow.F.Utils.List

open Lean

def Lean.Expr.toCExpr : Expr → CExpr
| .bvar i => .bvar i
| .fvar _ => .failed
| .mvar _ => .failed
| .sort l => .sort l
| .const n ll => .const n ll
| .app f a => .app (Expr.toCExpr f) (Expr.toCExpr a)
| .lam n t b i => .lam n (Expr.toCExpr t) (Expr.toCExpr b) i
| .forallE n t b i => .forallE n (Expr.toCExpr t) (Expr.toCExpr b) i
| .letE n t v b i => .letE n (Expr.toCExpr t) (Expr.toCExpr v) (Expr.toCExpr b) i
| .lit l => .lit l
| .proj t i b => .proj t i (Expr.toCExpr b)
| .mdata _ e => (Expr.toCExpr e)


partial def Lean.Expr.toCExprF (E : Expr) : CExpr :=
  let rec go : List Expr → List CExpr
      | [] => []
      | nx :: L =>
            match (Expr.consumeTypeAnnotations nx) with
            | .bvar i => .bvar i :: (go L)
            | .fvar _ => .failed :: (go L)
            | .mvar _ => .failed :: (go L)
            | .sort l => .sort l :: (go L)
            | .const n ll => .const n ll :: (go L)
            | .app f a =>
                  let r := go (f :: a :: L)
                  let (F,r2) := List.headD_tail r .failed
                  let (A,r3) := List.headD_tail r2 .failed
                  (.app F A) :: r3
            | .lam n t b i =>
                  let r := go (t :: b :: L)
                  let (T,r2) := List.headD_tail r .failed
                  let (B,r3) := List.headD_tail r2 .failed
                  (.lam n T B i) :: r3
            | .forallE n t b i =>
                  let r := go (t :: b :: L)
                  let (T,r2) := List.headD_tail r .failed
                  let (B,r3) := List.headD_tail r2 .failed
                  (.forallE n T B i) :: r3
            | .letE n t v b i =>
                  let r := go (t :: v :: b :: L)
                  let (T,r2) := List.headD_tail r .failed
                  let (V,r3) := List.headD_tail r2 .failed
                  let (B,r4) := List.headD_tail r3 .failed
                  (.letE n T V B i) :: r4
            | .lit l => .lit l :: (go L)
            | .proj t i b =>
                  let r := go (b :: L)
                  let B := List.headD r .failed
                  (.proj t i B) :: (List.drop 1 r)
            | .mdata _ e => go (e :: L)
  List.headD (go [E]) .failed



def CExpr.hasLNodes : CExpr → Bool
| .lnode _ _ _ => true
| .app f a => (CExpr.hasLNodes f) || (CExpr.hasLNodes a)
| .lam _ t b _ => (CExpr.hasLNodes t) || (CExpr.hasLNodes b)
| .forallE _ t b _ => (CExpr.hasLNodes t) || (CExpr.hasLNodes b)
| .letE _ t v b _ => (CExpr.hasLNodes t) || (CExpr.hasLNodes b) || (CExpr.hasLNodes v)
| .proj _ _ b => (CExpr.hasLNodes b)
| _ => false


partial def CExpr.hasLNodesF (E : CExpr) : Bool :=
      let rec go : List CExpr → Bool
      | [] => false
      | nx :: L =>
            match nx with
            | .lnode _ _ _ => true
            | .app f a => go (f :: a :: L)
            | .lam _ t b _ => go (t :: b :: L)
            | .forallE _ t b _ => go (t :: b :: L)
            | .letE _ t v b _ => go (t :: v :: b :: L)
            | .proj _ _ b => go (b :: L)
            | _ => go L
      go [E]

partial def CExpr.hasGNodesF (E : CExpr) : Bool :=
      let rec go : List CExpr → Bool
      | [] => false
      | nx :: L =>
            match nx with
            | .gnode _ _ => true
            | .app f a => go (f :: a :: L)
            | .lam _ t b _ => go (t :: b :: L)
            | .forallE _ t b _ => go (t :: b :: L)
            | .letE _ t v b _ => go (t :: v :: b :: L)
            | .proj _ _ b => go (b :: L)
            | _ => go L
      go [E]


partial def CExpr.hasNodesF (E : CExpr) : Bool :=
      E.hasLNodes || E.hasGNodesF

def CExpr.toExpr : CExpr → Option Expr
| .lnode _ _ _ | .gnode _ _ => .none
| .bvar i => .some (.bvar i)
| .sort l => .some (.sort l)
| .const n ll => .some (.const n ll)
| .app f a =>
      match CExpr.toExpr f, CExpr.toExpr a with
      | .some f', .some a' => .some (.app f' a')
      | _ , _ => .none
| .lam n t b B =>
      match CExpr.toExpr t, CExpr.toExpr b with
      | .some t', .some b' => .some (.lam n t' b' B)
      | _ , _ => .none
| .forallE n t b B =>
      match CExpr.toExpr t, CExpr.toExpr b with
      | .some t', .some b' => .some (.forallE n t' b' B)
      | _ , _ => .none
| .letE n t v b B =>
      match CExpr.toExpr t, CExpr.toExpr v, CExpr.toExpr b with
      | .some t', .some v', .some b' => .some (.letE n t' v' b' B)
      | _ , _, _ => .none
| .lit l => .some (.lit l)
| .proj t i b => (.proj t i) <$> (CExpr.toExpr b)
| .failed  => .none


partial def CExpr.toExprF (E : CExpr) : Option Expr :=
      let rec go : List CExpr → List (Option Expr)
      | [] => []
      | nx :: L =>
            match nx with
            | .lnode _ _ _ | .gnode _ _ => [.none]
            | .bvar i => .some (.bvar i) :: (go L)
            | .sort l => .some (.sort l) :: (go L)
            | .const n ll => .some (.const n ll) :: (go L)
            | .app f a =>
                  let r := go (f :: a :: L)
                  let (F,r2) := List.headD_tail r .none
                  let (A,r3) := List.headD_tail r2 .none
                  match F, A with
                  | .some f', .some a' => .some (.app f' a') :: r3
                  | _ , _ => [.none]
            | .lam n t b i =>
                  let r := go (t :: b :: L)
                  let (F,r2) := List.headD_tail r .none
                  let (A,r3) := List.headD_tail r2 .none
                  match F, A with
                  | .some t', .some b' => .some (.lam n t' b' i) :: r3
                  | _ , _ => [.none]
            | .forallE n t b i =>
                  let r := go (t :: b :: L)
                  let (F,r2) := List.headD_tail r .none
                  let (A,r3) := List.headD_tail r2 .none
                  match F, A with
                  | .some t', .some b' => .some (.forallE n t' b' i) :: r3
                  | _ , _ => [.none]
            | .letE n t v b i =>
                  let r := go (t :: v :: b :: L)
                  let (T,r2) := List.headD_tail r .none
                  let (V,r3) := List.headD_tail r2 .none
                  let (B,r4) := List.headD_tail r3 .none
                  match T, V, B with
                  | .some t', .some v', .some b' => .some (.letE n t' v' b' i) :: r4
                  | _ , _, _ => [.none]
            | .lit l => .some (.lit l) :: (go L)
            | .proj t i b =>
                  let r := go (b :: L)
                  let (B,r2) := List.headD_tail r .none
                  match B with
                  | .some b' => .some (.proj t i b') :: r2
                  | _ => [.none]
            | .failed => [.none]
      List.headD (go [E]) .none




def CExpr.getConstNames : CExpr → List Name
| .const n _ => [n]
| .app l r => (CExpr.getConstNames l) ++ (CExpr.getConstNames r)
| .lam _ l r _ => (CExpr.getConstNames l) ++ (CExpr.getConstNames r)
| .forallE _ l r _ =>  ((CExpr.getConstNames l) ++ (CExpr.getConstNames r))
| .letE _ t l r _ => (CExpr.getConstNames t) ++(CExpr.getConstNames l) ++ (CExpr.getConstNames r)
| .proj n _ e => n :: (CExpr.getConstNames e)
| .sort _ => []
| _ => []


-- todo : add accumulator
partial def CExpr.getConstNamesF (e : CExpr) : List Name :=
  let rec go : List CExpr → List Name
  | [] => []
  | x :: L =>
      match x with
      | .const n _ => n :: (go L)
      | .app l r => go (l :: r :: L)
      | .lam _ l r _ => go (l :: r :: L)
      | .forallE _ l r _ => go (l :: r :: L)
      | .letE _ t l r _ => go (t :: l :: r :: L)
      | .proj n _ e => n :: (go [e]) -- should be e :: L
      | _ => []
  go [e]


partial def CExpr.getLNodesMaxIdxF (E : CExpr) : Option Nat :=
      let rec go : List CExpr → List Nat
      | [] => []
      | nx :: L =>
            match nx with
            | .lnode i _ _ => i :: (go L)
            | .app f a =>
                  let r := go (f :: a :: L)
                  let (F,r2) := List.headD_tail r 0
                  let (A,r3) := List.headD_tail r2 0
                  if F > A
                  then F :: r3
                  else A :: r3
            | .lam _ t b _ =>
                  let r := go (t :: b :: L)
                  let (F,r2) := List.headD_tail r 0
                  let (A,r3) := List.headD_tail r2 0
                  if F > A
                  then F :: r3
                  else A :: r3
            | .forallE _ t b _ =>
                  let r := go (t :: b :: L)
                  let (F,r2) := List.headD_tail r 0
                  let (A,r3) := List.headD_tail r2 0
                  if F > A
                  then F :: r3
                  else A :: r3
            | .letE _ t v b _ =>
                  let r := go (t :: v :: b :: L)
                  let (T,r2) := List.headD_tail r 0
                  let (V,r3) := List.headD_tail r2 0
                  let (B,r4) := List.headD_tail r3 0
                  if T > V
                  then  if B > T
                        then B :: r4
                        else T :: r4
                  else  if B > V
                        then B :: r4
                        else V :: r4
            | .proj _ _ b => go (b :: L)
            | _ => go L
      match (go [E]) with
      | [M] => .some M
      | _ => .none


partial def CExpr.getGNodesMaxIdxF (E : CExpr) : Option Nat :=
      let rec go : List CExpr → List Nat
      | [] => []
      | nx :: L =>
            match nx with
            | .gnode i _ => i :: (go L)
            | .app f a =>
                  let r := go (f :: a :: L)
                  let (F,r2) := List.headD_tail r 0
                  let (A,r3) := List.headD_tail r2 0
                  if F > A
                  then F :: r3
                  else A :: r3
            | .lam _ t b _ =>
                  let r := go (t :: b :: L)
                  let (F,r2) := List.headD_tail r 0
                  let (A,r3) := List.headD_tail r2 0
                  if F > A
                  then F :: r3
                  else A :: r3
            | .forallE _ t b _ =>
                  let r := go (t :: b :: L)
                  let (F,r2) := List.headD_tail r 0
                  let (A,r3) := List.headD_tail r2 0
                  if F > A
                  then F :: r3
                  else A :: r3
            | .letE _ t v b _ =>
                  let r := go (t :: v :: b :: L)
                  let (T,r2) := List.headD_tail r 0
                  let (V,r3) := List.headD_tail r2 0
                  let (B,r4) := List.headD_tail r3 0
                  if T > V
                  then  if B > T
                        then B :: r4
                        else T :: r4
                  else  if B > V
                        then B :: r4
                        else V :: r4
            | .proj _ _ b => go (b :: L)
            | _ => go L
      match (go [E]) with
      | [M] => .some M
      | _ => .none



def CExpr.getApp (on : CExpr) : CExpr × List (CExpr) :=
      let rec go (as : List CExpr) : CExpr → CExpr × List (CExpr)
            | .app l r => go (r :: as) l
            | h => (h, as)
      go [] on


def CExpr.mkApp (h : CExpr) (args : List CExpr) : CExpr :=
      let rec go (sofar : CExpr) : List CExpr → CExpr
            | [] => sofar
            | a :: as => go (.app sofar a) as
      go h args

def CExpr.mkAppA (h : CExpr) (args : Array CExpr) : CExpr :=
      let rec go (sofar : CExpr) : Nat → CExpr
            | 0 => (.app sofar (args.get! (args.size - 1)))
            | n+1 => go (.app sofar (args.get! (args.size - 1 - n))) n
      go h args.size




def CExpr.replaceNoCache (f? : CExpr → Option CExpr) (e : CExpr) : CExpr :=
  match f? e with
  | some eNew => eNew
  | none      => match e with
    | .forallE n d b i => let d := replaceNoCache f? d; let b := replaceNoCache f? b; .forallE n d b i
    | .lam n d b i     => let d := replaceNoCache f? d; let b := replaceNoCache f? b; .lam n d b i
    | .letE n t v b i  => let t := replaceNoCache f? t; let v := replaceNoCache f? v; let b := replaceNoCache f? b; .letE n t v b i
    | .app f a         => let f := replaceNoCache f? f; let a := replaceNoCache f? a; .app f a
    | .proj n i b      => let b := replaceNoCache f? b; .proj n i b
    | e                => e


def CExpr.instantiateLevelParamsCore (s : Name → Option Level) (e : CExpr) : CExpr :=
  e.replaceNoCache replaceFn
where
  replaceFn (e : CExpr) : Option CExpr :=
    match e with
    | .const n us => .some (.const n (us.map fun u => u.substParams s))
    | sort u => .some (.sort (u.substParams s))
    | _ => .none

private def getParamSubst : List Name → List Level → Name → Option Level
  | p::ps, u::us, p' => if p == p' then some u else getParamSubst ps us p'
  | _,     _,     _  => none


def CExpr.instantiateLevelParams (e : CExpr) (paramNames : List Name) (lvls : List Level) : CExpr :=
  if paramNames.isEmpty || lvls.isEmpty then e else
    CExpr.instantiateLevelParamsCore (getParamSubst paramNames lvls) e


/-
**About levels**:
It seems that the typical use case of ↑ is when `e` is the value of a `.const`,
`paramNames` is the info contained in the `ConstantInfo` and `lvls` originates
from the `.const` constructor.
This is realy a glorified way of replacing parameters with concrete level values,
at all constants and sorts within the value expression.
Note that according to `getParamSubst` the way we do the substitution is that we look
up the index of the parameter in the list, and replace it by the level at same index
in the list of levels.

-/


def CExpr.updateFn : CExpr → CExpr → CExpr
  | .app f a, g => .app (CExpr.updateFn f g) a
  | _,           g => g
