

import LeanGrow.F.Utils.CExprTrie.Types
import LeanGrow.F.Utils.List


open Lean

private def insert_help [BEq α] (L : List (List Nat × α)) (new : α) (idx : Nat) : List (List Nat × α) :=
  let rec go (done : List (List Nat × α)) : List (List Nat × α) → List (List Nat × α)
    | [] => ([idx], new) :: done
    | nx :: more =>
        if nx.2 == new
        then ((List.orderedInsertOrLeave (· ≤ ·) idx nx.1, nx.2) :: done) ++ more
        else go (nx :: done) more
  go [] L


private def insert_help_projs (L : List (List Nat × Name × Nat × CExprTrie))
  (new : Name × Nat × CExpr) (idx : Nat) (insert : CExpr → Nat → CExprTrie → CExprTrie)
  : List (List Nat × Name × Nat × CExprTrie) :=
    let rec go (done : List (List Nat × Name × Nat × CExprTrie)) : List (List Nat ×  Name × Nat × CExprTrie) → List (List Nat × Name × Nat × CExprTrie)
      | [] => ([idx], new.1, new.2.1, insert new.2.2 idx .dead) :: done
      | nx :: more =>
          if nx.2.1 == new.1 && nx.2.2.1 == new.2.1
          then ((List.orderedInsertOrLeave (· ≤ ·) idx nx.1, nx.2.1, nx.2.2.1, insert new.2.2 idx nx.2.2.2) :: done) ++ more
          else go (nx :: done) more
    go [] L



namespace CExprTrie


partial def insert (ce : CExpr) (idx : Nat) : CExprTrie → CExprTrie
  | .dead =>
      match ce with
      | .app f a =>
          .br [] [] [] [] [] []  (insert f idx .dead) (insert a idx .dead) [idx]  .dead .dead []  .dead .dead []  .dead .dead .dead [] []
      | .lam _ f a _ =>
          .br [] [] [] [] [] []  .dead .dead []  (insert f idx .dead) (insert a idx .dead) [idx]  .dead .dead []  .dead .dead .dead [] []
      | .forallE _ f a _ =>
          .br [] [] [] [] [] []  .dead .dead []  .dead .dead []  (insert f idx .dead) (insert a idx .dead) [idx]  .dead .dead .dead [] []
      | .letE _ f a z _ =>
          .br [] [] [] [] [] []  .dead .dead []  .dead .dead []  .dead .dead []  (insert f idx .dead) (insert a idx .dead) (insert z idx .dead) [idx] []
      | .proj n i e =>
          .br [] [] [] [] [] []  .dead .dead []  .dead .dead []  .dead .dead []  .dead .dead .dead [] [([idx],n,i,(insert e idx .dead))]
      | .lnode p _ t =>
          .br [([idx],p,t)] [] [] [] [] []  .dead .dead []  .dead .dead []  .dead .dead []  .dead .dead .dead [] []
      | .gnode p _ =>
          .br [] [([idx],p)] [] [] [] []  .dead .dead []  .dead .dead []  .dead .dead []  .dead .dead .dead [] []
      | .bvar p =>
          .br [] [] [([idx],p)] [] [] []  .dead .dead []  .dead .dead []  .dead .dead []  .dead .dead .dead [] []
      | .sort p  =>
          .br [] [] [] [([idx],p)] [] []  .dead .dead []  .dead .dead []  .dead .dead []  .dead .dead .dead [] []
      | .const n l =>
          .br [] [] [] [] [([idx], n,l)] []  .dead .dead []  .dead .dead []  .dead .dead []  .dead .dead .dead [] []
      | .lit p  =>
          .br [] [] [] [] [] [([idx],p)]  .dead .dead []  .dead .dead []  .dead .dead []  .dead .dead .dead [] []
      | .failed => .dead
  | .br lnodes gnodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs =>
      match ce with
      | .app f a  =>
          .br lnodes gnodes bvars sorts consts lits (insert f idx apf) (insert a idx apa) (List.orderedInsertOrLeave (· ≤ ·) idx api) laf laa lai alf ala ali lef lea lez lei projs
      | .lam _ f a _  =>
          .br lnodes gnodes bvars sorts consts lits apf apa api (insert f idx laf) (insert a idx laa) (List.orderedInsertOrLeave (· ≤ ·) idx lai) alf ala ali lef lea lez lei projs
      | .forallE _ f a _  =>
          .br lnodes gnodes bvars sorts consts lits apf apa api (laf) (laa) (lai) (insert f idx alf) (insert a idx ala) (List.orderedInsertOrLeave (· ≤ ·) idx ali) lef lea lez lei projs
      | .letE _ f a z _ =>
          .br lnodes gnodes bvars sorts consts lits apf apa api laf laa lai alf ala ali (insert f idx lef) (insert a idx lea) (insert z idx lez) (List.orderedInsertOrLeave (· ≤ ·) idx lei) projs
      | .proj n i e =>
          .br lnodes gnodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei (insert_help_projs projs (n,i,e) idx insert)
      | .lnode p _ t =>
          .br (insert_help lnodes (p,t) idx) gnodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs
      | .gnode p _ =>
          .br lnodes (insert_help gnodes p idx) bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs
      | .bvar p =>
          .br lnodes gnodes (insert_help bvars p idx) sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs
      | .sort p  =>
          .br lnodes gnodes bvars (insert_help sorts p idx) consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs
      | .const n l =>
          .br lnodes gnodes bvars sorts (insert_help consts (n,l) idx) lits apf apa api laf laa lai alf ala ali lef lea lez lei projs
      | .lit p  =>
          .br lnodes gnodes bvars sorts consts (insert_help lits p idx) apf apa api laf laa lai alf ala ali lef lea lez lei projs
      | .failed => .dead


def ofList (L : List (Nat × CExpr)) : CExprTrie :=
  L.foldl (fun x y => CExprTrie.insert y.2 y.1 x) .dead
