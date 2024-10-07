
import LeanGrow.F.Data.CExpr.Types


open Lean


inductive CExprTrie.Branch (α : Type _) where
| ofNode (idx : Nat) (indices : List α)
| ofBvar (idx : Nat) (indices : List α)
| ofSort (l : Level) (indices : List α)
| ofConst (n : Name) (indices : List α) -- (ll : List Level)
| ofApp (link_f link_a : Nat)
| ofLam (name : Name) (link_t link_b : Nat) (info : BinderInfo)
| ofForall (name : Name) (link_t link_b : Nat) (info : BinderInfo)
| ofLet (name : Name) (link_t link_v link_b : Nat) (info : Bool)
| ofLit (lit : Literal) (indices : List α)
| ofProj (name : Name) (idx link_e : Nat)
| ofFailed
deriving BEq, Inhabited, Repr


def CExprTrie (α : Type _) := List (Nat × List (CExprTrie.Branch α))

-- deriving fails, hence :

instance [BEq α] : BEq (CExprTrie α) where
  beq := List.instBEq.beq

instance [Inhabited α] : Inhabited (CExprTrie α) where
  default := instInhabitedList.default

instance [Repr α] : Repr (CExprTrie α) where
  reprPrec := instReprList.reprPrec
