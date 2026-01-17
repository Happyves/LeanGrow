

# Notes

- use the upper case versions like `ForallLetTelescopeWW` from Utils/Lean/LocalContext
  WARNING: there are specific versions that use workers

- moved `forallMetaTagTelescope` to Utils.MetaAPI, and Capitalised

- check we use rec versions of mvarifying and worker collecting etc.

- `mvarifyTnodesRecWiContextIn` to `mvarifyTnodesRec`, and does not add Ltx to mvars

- refer to revert tests : we should add deps for reverts at rw/induction

- check if class and add inst binder, as other ops depend on it

- use `Lean.LocalInstances.cleanPatches` between grow iterations?

- be careful when using PaIn ops : shouldn't be done under external worker local instances, as we delete them after ops

- use `Lean.Meta.resetDefEqPermCaches` and `resetSynthInstanceCache` ?

# Todo 

- PaIn.build : when making lambdas, should check if class and make binder
  instance implicit, as other parts require this assumption...

- PaIn intersection that returns indices (indices of one of them, to be chosen)
  also, intersection up to unification ; isn't this part of Core, as we have to
  load lnode types ...

# Long term

- Return to non-TR version from Alpha for PathIndices

- Use Index structure

- matches with hyp-patterns for scoring for induction should point to which fvars
  should be reverted to make the induction motive

- at scoring for sampled types that are types, record value so that at scoring
  we use these for unodes ...
