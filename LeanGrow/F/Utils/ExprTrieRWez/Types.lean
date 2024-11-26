
import LeanGrow.F.Data.CExpr.Types


open Lean


inductive CExprTrie.Branch (α : Type _) where
| ofLNode (idx : Nat) (tag : Option Nat) (indices : List α) (ref : Nat)
| ofGNode (idx : Nat) (indices : List α) (ref : Nat)
| ofBvar (idx : Nat) (indices : List α) (ref : Nat)
| ofSort (l : Level) (indices : List α) (ref : Nat)
| ofConst (n : Name) (ll : List Level) (indices : List α) (ref : Nat)
| ofApp (link_f link_a : Nat) (indDirs : List α) (f_brDirs a_brDirs : List Nat) (ref : Nat)
| ofLam (link_t link_b : Nat) (indDirs : List α) (f_brDirs a_brDirs : List Nat) (ref : Nat)
| ofForall (link_t link_b : Nat) (indDirs : List α) (f_brDirs a_brDirs : List Nat) (ref : Nat)
| ofLet (link_t link_v link_b : Nat) (indDirs : List α) (f_brDirs a_brDirs z_brDirs : List Nat) (ref : Nat)
| ofLit (lit : Literal) (indices : List α) (ref : Nat)
| ofProj (name : Name) (idx link_e : Nat) (indDirs : List α) (brDirs : List Nat) (ref : Nat)
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
