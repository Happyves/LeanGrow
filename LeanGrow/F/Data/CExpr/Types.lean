
import Lean.Expr

open Lean

inductive OriginalData where
| missing
| ofBvar : Nat → OriginalData
| ofFvar (fvarId : FVarId)
deriving Inhabited, BEq, Repr

inductive CExpr where
| node : Nat → OriginalData → CExpr
| bvar : Nat → CExpr
| sort : Level → CExpr
| const : Name → List Level → CExpr
| app : CExpr → CExpr → CExpr
| lam : Name → CExpr → CExpr → BinderInfo → CExpr
| forallE : Name → CExpr → CExpr → BinderInfo → CExpr
| letE : Name → CExpr → CExpr → CExpr → Bool → CExpr
| lit : Literal → CExpr
| proj : Name → Nat → CExpr → CExpr
| failed : CExpr
deriving Inhabited, BEq, Repr


inductive EmbedData where
| nonInst (t : CExpr) (parents : Array Nat)
| inst (t : CExpr) (parents : Array Nat)
deriving BEq, Inhabited, Repr

def EmbedData.cexpr : EmbedData → CExpr
| .nonInst ce _ => ce
| .inst ce _ => ce


inductive LCExpr where
| node : LCExpr
| bvar : Nat → LCExpr
| sort : Level → LCExpr
| const : Name  → LCExpr
| app : Nat → LCExpr
| lam : Name → CExpr → CExpr → BinderInfo → CExpr
| forallE : Name → CExpr → CExpr → BinderInfo → CExpr
| letE : Name → CExpr → CExpr → CExpr → Bool → CExpr
| lit : Literal → CExpr
| proj : Name → Nat → CExpr → CExpr
| failed : CExpr
deriving Inhabited, BEq, Repr
