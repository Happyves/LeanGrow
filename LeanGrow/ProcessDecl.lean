

import LeanGrow.CExpr
import LeanGrow.DAGstruct
import Mathlib
import Qq

open Lean

--#exit

/-- Dag nodes ordering from 0 to size - 1-/
def orderHyps_wBvar (hyps : List (Expr × miniBind)) : SizedDAG CExpr Nat :=
  let rec abstractBvars_collectParents (e : Expr) (f : miniBind) (inner_count : Option Nat) (len : Nat) : CExpr × List Nat:=
    let res :=
        match e with
        | .bvar i => match inner_count with
                    | .none => (.node (len - 1 - i) (.ofBvar i), [len - 1 - i])
                    | .some x => if i ≤ x then (.bvar i, []) else (.node (len + x - i) (.ofBvar i), [len + x - i])
        | .app l r => let L := abstractBvars_collectParents l .default inner_count len ;
                      let R := abstractBvars_collectParents r .default inner_count len;
                      (.app L.1 R.1, L.2 ++ R.2)
        | .lam n l r B => let L := abstractBvars_collectParents l .default inner_count len;
                          let R := abstractBvars_collectParents r .default (if inner_count = .none then .some 0 else inner_count.map Nat.succ) len ;
                          (.lam n L.1 R.1 B , L.2 ++ R.2)
        | .forallE n l r B => let L := abstractBvars_collectParents l .default inner_count len ;
                              let R := abstractBvars_collectParents r .default (if inner_count = .none then .some 0 else inner_count.map Nat.succ) len ;
                              (.forallE n L.1 R.1 B , L.2 ++ R.2)
        | .mdata _ e => let r := abstractBvars_collectParents e .default inner_count len ; (r.1, r.2)
        | .proj n i e => let r := abstractBvars_collectParents e .default inner_count len ; (.proj n i r.1, r.2)
        | x => (x.toCExpr, [])
    match f with
    | .inst => (.wrapInst res.1, res.2)
    | _ => res

  let rec go (l : List (Expr × miniBind)) (count : Nat) : (DAG CExpr Nat) × Nat :=
    match l with
    | [] => ([], count)
    | h :: rest =>
          let (res, deps) := abstractBvars_collectParents h.1 h.2 .none (count)
          let sofar := go rest (count + 1)
          (⟨count, res, deps⟩ :: sofar.1, sofar.2)

  let (d, n) := go hyps 0
  ⟨n, d⟩


#exit

open Qq

def e := q(∀ n : Nat, Prime n → ∀ m : Nat, Odd m → (h : Nat.Coprime n m) → ((fun (x y : Nat) (H : Nat.Coprime n m) => 1+1=2) 1 1 h) → Nat)

#eval e


#eval naiveGetHyps e


#eval orderHyps_wBvar (naiveGetHyps e)


def e' := q(∀ n : Nat, ((fun (x y : Nat) => x + n + y = 42) 2 3) → True)

#eval orderHyps_wBvar (naiveGetHyps e')


#check LocalContext

--def unify_expr (target main : DAG Expr)
