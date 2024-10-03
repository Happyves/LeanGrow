
import LeanGrow.F.Data.CExpr.API
import LeanGrow.F.Utils.DAG.Types


open Lean



/-- Dag nodes ordering from 0 to size - 1-/
def orderHyps_wBvar (hyps : List (Expr × Bool)) : List (Nat × CExpr × List Nat) :=
  let rec abstractBvars_collectParents (E : Expr) (f : Bool) (inner_count : Option Nat) (len : Nat) : CExpr × List Nat :=
    let rec go1 (f : Bool) (inner_count : Option Nat) (len : Nat) (cache_exp : (List CExpr)) (cache_pars : (List Nat)) : List Expr → CExpr × List Nat
      | [] =>
          let ce := List.headD cache_exp .failed
          (ce, cache_pars)
      | e :: more =>
          match e with
          | .app (.app (.const `optParam _) e) _ => go1 f inner_count len cache_exp cache_pars (e :: more)  -- got wierd problems in source file gen otherwise
          | .app (.app (.const `outParam _) e) _ => go1 f inner_count len cache_exp cache_pars (e :: more)
          | .bvar i => match inner_count with
                      | .none => (.node (len - 1 - i) (.ofBvar i), [len - 1 - i])
                      | .some x => if i ≤ x then (.bvar i, []) else (.node (len + x - i) (.ofBvar i), [len + x - i])
          | .app l r => let L := go1 false inner_count len ache_exp cache_pars (l :: ) ;
                        let R := abstractBvars_collectParents r false inner_count len;
                        (.app L.1 R.1, L.2 ++ R.2)
          | .lam n l r B => let L := abstractBvars_collectParents l false inner_count len;
                            let R := abstractBvars_collectParents r false (if inner_count = .none then .some 0 else inner_count.map Nat.succ) len ;
                            (.lam n L.1 R.1 B , L.2 ++ R.2)
          | .forallE n l r B => let L := abstractBvars_collectParents l false inner_count len ;
                                let R := abstractBvars_collectParents r false (if inner_count = .none then .some 0 else inner_count.map Nat.succ) len ;
                                (.forallE n L.1 R.1 B , L.2 ++ R.2)
          | .mdata _ e => let r := abstractBvars_collectParents e false inner_count len ; (r.1, r.2)
          | .proj n i e => let r := abstractBvars_collectParents e false inner_count len ; (.proj n i r.1, r.2)
          | x => (x.toCExpr, [])

  let rec go (l : List (Expr × Bool)) (count : Nat) : (DAG CExpr Nat) × Nat :=
    match l with
    | [] => ([], count)
    | h :: rest =>
          let (res, deps) := abstractBvars_collectParents h.1 h.2 .none (count)
          let sofar := go rest (count + 1)
          let deps_fix := List.dedup deps
          (⟨count, res, deps_fix⟩ :: sofar.1, sofar.2)

  let (d, n) := go hyps 0
  ⟨n, d⟩
