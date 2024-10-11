
import LeanGrow.F.Data.CExpr.API
import LeanGrow.F.Utils.DAG.Types
import LeanGrow.F.Utils.List

open Lean

/-- Expects `hyps` in reverse order as in thm type-/
partial def ThmType_ToDAG (hyps : List (Expr × Bool)) (l_len : Nat) (goal : Expr) : List (Nat × CExpr × Bool × List Nat) × (CExpr × List Nat) :=
  let inc_helper : Option Nat → Option Nat
    | .none => .some 0
    | .some x => .some (x+1)

  let rec abstractBvars_collectParents (E : Expr) (offset : Nat → Nat) : CExpr × List Nat :=
    let rec go1 (offset : Nat → Nat) (cache_pars : (List Nat)) (dinfo : List (Option Nat)) : List Expr → (List CExpr) × List Nat
      | [] =>
          ([], cache_pars)
      | e :: more =>
          match e with
          | .app (.app (.const `optParam _) e) _ => go1 offset cache_pars dinfo (e :: more)  -- got wierd problems in source file gen otherwise
          | .app (.app (.const `outParam _) e) _ => go1 offset cache_pars dinfo (e :: more)
          | .bvar i =>
                let (d?,ndi) := List.headD_tail dinfo .none
                match d? with
                | .none =>
                    let (re,rp) := go1 offset (List.orderedInsertOrLeave (· ≤ · ) (offset (i+1)) cache_pars) ndi more
                    (((CExpr.lnode (offset (i+1))) (.ofBvar i)) :: re, rp)
                | .some d =>
                    if i ≤ d
                    then
                      let (re,rp) := go1 offset cache_pars ndi more
                      ((.bvar i) :: re, rp)
                    else
                      let (re,rp) := go1 offset (List.orderedInsertOrLeave (· ≤ · ) (offset (i - d)) cache_pars) ndi more
                      (((CExpr.lnode (offset (i - d))) (.ofBvar i)) :: re, rp)
          | .app l r => let d? := List.headD dinfo .none
                        let (re,rp) := go1 offset cache_pars (d? :: dinfo) (l :: r :: more)
                        let (L,re2) := List.headD_tail re .failed
                        let (R,re3) := List.headD_tail re2 .failed
                        (.app L R :: re3, rp)
          | .lam n l r B => let (d?,ndi) := List.headD_tail dinfo .none
                            let (re,rp) := go1 offset cache_pars (d? :: (inc_helper d?) :: ndi) (l :: r :: more)
                            let (L,re2) := List.headD_tail re .failed
                            let (R,re3) := List.headD_tail re2 .failed
                            (.lam n L R B :: re3, rp)
          | .forallE n l r B => let (d?,ndi) := List.headD_tail dinfo .none
                                let (re,rp) := go1 offset cache_pars (d? :: (inc_helper d?) :: ndi) (l :: r :: more)
                                let (L,re2) := List.headD_tail re .failed
                                let (R,re3) := List.headD_tail re2 .failed
                                (.forallE n L R B :: re3, rp)
          | .mdata _ e => go1 offset cache_pars dinfo (e :: more)
          | .proj n i e => let (re,rp) := go1 offset cache_pars dinfo (e :: more)
                           let (E,r2) :=  List.headD_tail re .failed
                           (.proj n i E :: r2, rp)
          -- we don't expect `let` or mvar or fvars in thm types ...
          | x =>
              let ndi := List.tailD dinfo []
              let (cs, ps) := go1 offset cache_pars ndi (more)
              (x.toCExpr :: cs, ps)
    let (ce, ps) := go1 offset [] [.none] [E]
    (List.headD ce .failed, ps)

  let rec go2 (l : List (Expr × Bool)) (count : Nat) (cache : List (Nat × CExpr × Bool × List Nat)) : List (Nat × CExpr × Bool × List Nat) × (CExpr × List Nat) :=
    match l with
    | [] =>
        let (res, deps) := abstractBvars_collectParents goal (fun o => l_len - o)
        (cache, (res, deps))
    | h :: rest =>
          let (res, deps) := abstractBvars_collectParents h.1 (fun o => count - o)
          go2 rest (count - 1) (⟨count, res, h.2, deps⟩ :: cache)

  go2 hyps (l_len - 1) []
