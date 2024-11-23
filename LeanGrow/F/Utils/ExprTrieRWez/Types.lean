
import LeanGrow.F.Data.CExpr.Types


open Lean


inductive CExprTrie.Branch (α : Type _) where
| ofLNode (idx : Nat) (tag : Option Nat) (indices : List α)
| ofGNode (idx : Nat) (indices : List α)
| ofBvar (idx : Nat) (indices : List α)
| ofSort (l : Level) (indices : List α)
| ofConst (n : Name) (ll : List Level) (indices : List α)
| ofApp (link_f link_a : Nat) (indDirs : List α) (f_brDirs a_brDirs : List Nat)
| ofLam (link_t link_b : Nat) (indDirs : List α) (f_brDirs a_brDirs : List Nat)
| ofForall (link_t link_b : Nat) (indDirs : List α) (f_brDirs a_brDirs : List Nat)
| ofLet (link_t link_v link_b : Nat) (indDirs : List α) (f_brDirs a_brDirs z_brDirs : List Nat)
| ofLit (lit : Literal) (indices : List α)
| ofProj (name : Name) (idx link_e : Nat) (indDirs : List α) (brDirs : List Nat)
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
