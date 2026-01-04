

# Notes

- use the upper case versions like `ForallLetTelescopeWW` from Utils/Lean/LocalContext
  WARNING: there are specific versions that use workers

- moved `forallMetaTagTelescope` to Utils.MetaAPI, and Capitalised

- check we use rec versions of mvarifying and worker collecting etc.

- `mvarifyTnodesRecWiContextIn` to `mvarifyTnodesRec`, and does not add Ltx to mvars

- refer to revert tests : we should add deps for reverts at rw/induction

- check if class and add inst binder, as other ops depend on it

- use `Lean.LocalInstances.cleanPatches` between grow iterations?

# Todo 

- add workers to testing

# Long term

- matches with hyp-patterns for scoring for induction should point to which fvars
  should be reverted to make the induction motive
