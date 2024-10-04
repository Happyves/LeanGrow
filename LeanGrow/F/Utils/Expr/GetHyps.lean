
import Lean.Expr

open Lean

def Lean.Expr.getHypsGoal (ty : Expr) : (List (Expr × Bool)) × Expr :=
  let rec go (cache : List (Expr × Bool)) : Expr → (List (Expr × Bool)) × Expr
    | .forallE _ h b i =>
          match i with
          | .instImplicit => go ((h , true) :: cache) b
          | _ => go ((h , false) :: cache) b
    | .mdata  _ e => go cache e
    | e => (cache, e)
  go [] ty
