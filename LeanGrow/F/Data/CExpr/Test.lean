

import LeanGrow.F.Data.CExpr.Types
import LeanGrow.F.Utils.List

open Lean

set_option trace.compiler.ir.result true

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
            match ( nx) with -- Expr.consumeTypeAnnotations ?!?!
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


partial def Lean.Expr.toCExprF' (E : @& Expr) : CExpr :=
  let rec go : @& List Expr → List CExpr
      | [] => []
      | nx :: L =>
            match ( nx) with -- Expr.consumeTypeAnnotations ?!?!
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


/-

[result]
def CExpr.hasLNodesF.go (x_1 : obj) : u8 :=
  case x_1 : obj of
  List.nil →
    let x_2 : u8 := 0;
    ret x_2
  List.cons →
    let x_3 : obj := proj[0] x_1;
    inc x_3;
    case x_3 : obj of
    CExpr.lnode →
      dec x_3;
      dec x_1;
      let x_4 : u8 := 1;
      ret x_4
    CExpr.app →
      let x_5 : u8 := isShared x_1;     -- shouldn't ever be the case in single threaded context ?!?
      case x_5 : u8 of
      Bool.false →
        let x_6 : obj := proj[0] x_1;   -- pointless
        dec x_6;                        -- pointless
        let x_7 : u8 := isShared x_3;
        case x_7 : u8 of
        Bool.false →
          let x_8 : obj := proj[1] x_3; -- `a`
          set x_1[0] := x_8;            -- changes x_1 = `nx :: L` to `a :: L`
          setTag x_3 := 1;              -- x_3 was an Expr constructor with 2 fields, so we can reusit as List.cons, by changing its tag
          set x_3[1] := x_1;            -- x_3 first field already points to `f`, so by reinterpreting it as a List.cons and setting the second field to `a :: L ` we get `f :: a :: L`
          let x_9 : u8 := CExpr.hasLNodesF.go x_3;
          ret x_9

-/
