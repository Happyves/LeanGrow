
import LeanGrow.F.Data.CExpr.Types


#check 1

inductive CstInfo where
| wVal (levelParams : List Lean.Name) (type : CExpr) (val : CExpr)
| noVal (levelParams : List Lean.Name) (type : CExpr)
| struc (levelParams : List Lean.Name) (type : CExpr) (ctorName : Lean.Name)
deriving Inhabited, BEq, Repr

def CstInfo.type : CstInfo → CExpr
  | .wVal _ t _ => t
  | .noVal _ t => t
  | .struc _ t _ => t

def CstInfo.levelParams : CstInfo → List Lean.Name
  | .wVal t _ _ => t
  | .noVal t _ => t
  | .struc t _ _ => t


/-
Notes:

- Don't forget to recognize structures when building the Trie
-- also get rid of annotations to account for Expr.consumeTypeAnnotations (in inferProj)


-/
