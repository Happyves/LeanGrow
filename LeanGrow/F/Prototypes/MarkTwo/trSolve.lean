

import LeanGrow.F.Prototypes.MarkTwo.trTypes
import LeanGrow.F.Utils.Array
import LeanGrow.F.Data.CExpr.API

open Lean

/-
Backsteps should delete one goal, and possibly (probably) add new goals.
Unisteps should delete goals.
If there are no active goals, then we may assemble.
-/

/-- Won't be needed in final version, as we expct to add additional
gnodes as lets, but we'll still have to assemble them -/
partial def unfoldAddedGnodes (ltx_assemmbly : List (Nat × Name × Array CExpr)) (e : CExpr) : CExpr :=
  let rec go (e : CExpr) : CExpr := -- add API for this =__=
    match e with
    | .app f a =>  (.app (go f) (go a))
    | .lam n f a i => .lam n (go f) (go a) i
    | .forallE n f a i => .forallE n (go f) (go a) i
    | .letE n f a z i => .letE n (go f) (go a) z i
    | .proj n i f => .proj n i (go f)
    | .gnode i _ =>
        match ltx_assemmbly.find? (fun (id,_,_) => id == i) with
        | .some (_,n,emb) => go (CExpr.mkAppA (.const n []) emb)
        | .none => e
    | x => x
  go e



partial def BackTree.assemble (ltx_assemmbly : List (Nat × Name × Array CExpr)) : BackTree → CExpr
  | .fail => .failed
  | .ofGoal _ _ => .failed
  | .ofAssign ce => unfoldAddedGnodes ltx_assemmbly ce
  | .ofBack _ n _ _ args =>
        let mk := args.mapF (BackTree.assemble ltx_assemmbly)
        CExpr.mkAppA (.const n []) mk -- fix levels
