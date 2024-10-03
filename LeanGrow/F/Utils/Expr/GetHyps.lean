
import Lean.Expr

open Lean

inductive miniBind where
| default | inst | impl


def naiveGetHyps (ty : Expr) : (List (Expr × miniBind)) :=
  match ty with
  | .forallE _ h b i =>
        let H := (naiveGetHyps b)
        match i with
        | .instImplicit => (h , .inst) :: H
        | .default => (h, .default)  :: H
        | _ => (h, .impl)  :: H
  | .mdata  _ e => naiveGetHyps e
  | _ => []


#check Expr.getForallBody
