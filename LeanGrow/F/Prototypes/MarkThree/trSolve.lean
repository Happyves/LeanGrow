

import LeanGrow.F.Prototypes.MarkThree.trTypes
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


/-
Thoughts:

- maintain a list of pairs of solutions terms and a list of uni-ids they require

- unifications (uni-ids) clash if they assign non-equal values to the same lnode
  (given by a tag and position)

- For .ofGoal, recurse on the sols, and join the results. So if a goal isn't solved,
  the return should be empty

- For .ofBack, recurse on the args and make the cartesian product of results,
  which should then be pruned on unification-clashes. Then, form new terms that
  are applications of the back-thm to the elements of the catesian prod, and join
  the uni-ids corresponding to the product to be the new uni-ids list constraint.
  We want that when one of the args returns empty solutions, to return empt solutions

- For .ofAssign, we should postpone somehow ? Or not, just keep the lnodes. We should
  wait for the term to be fully assembled, at which stage we replace the lnodes by the
  values set by unifications (and fix levels ?)

- for .ofUni, we retrieve the value as term, and add the uni-id and the other data
  to the constraint context

- for .ofPropa, recurse on the sols, join the results, and (as opposed to .ofGoal)
  add the uni-id to each results constraint. Don't know if there can be unification
  clashes here, so do a clash check anyway ?

OR ... we can collect the information which lnodes gets fixed with which values durring
unification propagation. Then, we can tell in advance if unifications clash or not,
without working on the BackTree

-/

#exit
partial def BackTree.assemble?
  (ltx_assemmbly : List (Nat × Name × Array CExpr)) (bt : BackTree) : List CExpr :=
  let rec go
