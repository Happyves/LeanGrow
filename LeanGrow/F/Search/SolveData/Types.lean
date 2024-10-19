
import LeanGrow.F.Search.BackwardData.Types


#check 1

/-
In the current state of things, an actual solution is when we make
a backstep that corresponds to unifying a ltx gnode with a goal,
such that propagation doesn't prevent the solution (clash at previously unified stuff)
and no further goals are generated from propagation

Consider the running example of:
"For example, we could have a first appli of le_trans yielding goals Nat,
1 ≤ .lnode 1 0 and .lnode 1 0 ≤ 4.  We then apply a second le_trans to the second
subgoal, so as to get new goals Nat, 1 ≤ .lnode 1 1 and .lnode 1 1 ≤ .lnode 1 0.
If we have `p : 2 ≤ 3` in the context, and we unify it with .lnode 1 1 ≤ .lnode 1 0, then we should
produce a backstep that has the following data : it solves the initial goal,
produces new subgoals 1 ≤ 2 and 3 ≤ 4, and assigns solutions 2 3 and p."

Here, if we unify a gnode with 1 ≤ 2, then this won't spawn further goals
and we may consider the goal to truely be solved.


A backstep/thm-appli is solved if all its subgoals are.
-/
