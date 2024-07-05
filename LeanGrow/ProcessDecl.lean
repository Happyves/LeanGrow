

import LeanGrow.CExpr
import LeanGrow.DAGstruct
import Mathlib
import Qq

open Lean

inductive miniBind where
| default | inst | impl


def naiveGetHyps (ty : Expr) : (List Expr) × (List miniBind) :=
  match ty with
  | .forallE _ h b i =>
        let (H,I) := (naiveGetHyps b)
        match i with
        | .default => (h :: H, .default :: I)
        | .instImplicit => (h :: H, .inst :: I)
        | _ => (h :: H, .impl :: I)
  | .mdata  _ e => naiveGetHyps e
  | _ => ([],[])


--#exit

/-- Dag nodes ordering from 0 to size - 1-/
def orderHyps_wBvar (hyps : List Expr) : SizedDAG CExpr Nat :=
  let rec abstractBvars_collectParents (e : Expr) (inner_count : Option Nat) (len : Nat) : CExpr × List Nat:=
    match e with
    | .bvar i => match inner_count with
                 | .none => (.node (len - 1 - i) (.ofBvar i), [len - 1 - i])
                 | .some x => if i ≤ x then (.bvar i, []) else (.node (len + x - i) (.ofBvar i), [len + x - i])
    | .app l r => let L := abstractBvars_collectParents l inner_count len ;
                  let R := abstractBvars_collectParents r inner_count len;
                  (.app L.1 R.1, L.2 ++ R.2)
    | .lam n l r B => let L := abstractBvars_collectParents l inner_count len;
                      let R := abstractBvars_collectParents r (if inner_count = .none then .some 0 else inner_count.map Nat.succ) len ;
                      (.lam n L.1 R.1 B , L.2 ++ R.2)
    | .forallE n l r B => let L := abstractBvars_collectParents l inner_count len ;
                          let R := abstractBvars_collectParents r (if inner_count = .none then .some 0 else inner_count.map Nat.succ) len ;
                          (.forallE n L.1 R.1 B , L.2 ++ R.2)
    | .mdata _ e => let r := abstractBvars_collectParents e inner_count len ; (r.1, r.2)
    | .proj n i e => let r := abstractBvars_collectParents e inner_count len ; (.proj n i r.1, r.2)
    | x => (x.toCExpr, [])

  let rec go (l : List Expr) (count : Nat) : (DAG CExpr Nat) × Nat :=
    match l with
    | [] => ([], count)
    | h :: rest =>
          let (res, deps) := abstractBvars_collectParents h .none (count)
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
