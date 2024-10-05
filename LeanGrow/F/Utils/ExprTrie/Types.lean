
import LeanGrow.F.Data.CExpr.Types


open Lean


inductive CExprTrie.Branch where
| ofNode (idx : Nat) (indices : List Nat)
| ofBvar (idx : Nat) (indices : List Nat)
| ofSort (l : Level) (indices : List Nat)
| ofConst (n : Name) (indices : List Nat) -- (ll : List Level)
| ofApp (link_f link_a : Nat)
| ofLam (name : Name) (link_t link_b : Nat) (info : BinderInfo)
| ofForall (name : Name) (link_t link_b : Nat) (info : BinderInfo)
| ofLet (name : Name) (link_t link_v link_b : Nat) (info : Bool)
| ofLit (lit : Literal) (indices : List Nat)
| ofProj (name : Name) (idx link_e : Nat)
| ofFailed
deriving BEq, Inhabited, Repr


def CExprTrie := List (Nat × List CExprTrie.Branch)
deriving BEq, Inhabited, Repr
