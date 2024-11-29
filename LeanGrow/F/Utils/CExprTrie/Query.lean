
import LeanGrow.F.Utils.CExprTrie.Types
import LeanGrow.F.Utils.List


open Lean

namespace CExprTrie


def find? (ce : CExpr) (T : CExprTrie) : List Nat :=
  let rec go (ce : CExpr) : CExprTrie → List Nat
    | .dead => []
    | .br lnodes gnodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs =>
      match ce with
      | .app f a =>
          match api with
          | [] => []
          | _ => List.orderedIntersect (· ≤ ·) (find? f apf) (find? a apa)
      | .lam _ f a _  =>
          match lai with
          | [] => []
          | _ => List.orderedIntersect (· ≤ ·) (find? f laf) (find? a laa)
      | .forallE _ f a _  =>
          match ali with
          | [] => []
          | _ => List.orderedIntersect (· ≤ ·) (find? f alf) (find? a ala)
      | .letE _ f a z _ =>
          match lei with
          | [] => []
          | _ => List.orderedIntersect (· ≤ ·) (List.orderedIntersect (· ≤ ·) (find? f lef) (find? a lea)) (find? z lez)
      | .proj n i e =>
          let found := List.find? (fun x => x.2.1 == n && x.2.2.1 == i) projs
          match found with
          | .none => []
          | .some x => find? e x.2.2.2
      | .lnode p _ t =>
          let found := List.find? (fun x => x.2.1 == p && x.2.2 == t) lnodes
          match found with
          | .none => []
          | .some x => x.1
      | .gnode p _ =>
          let found := List.find? (fun x => x.2 == p ) gnodes
          match found with
          | .none => []
          | .some x => x.1
      | .bvar p =>
          let found := List.find? (fun x => x.2 == p ) bvars
          match found with
          | .none => []
          | .some x => x.1
      | .sort p  =>
          let found := List.find? (fun x => x.2 == p ) sorts
          match found with
          | .none => []
          | .some x => x.1
      | .const n l =>
          let found := List.find? (fun x => x.2.1 == n && x.2.2 == l ) consts
          match found with
          | .none => []
          | .some x => x.1
      | .lit p  =>
          let found := List.find? (fun x => x.2 == p ) lits
          match found with
          | .none => []
          | .some x => x.1
      | .failed => []
  go ce T
