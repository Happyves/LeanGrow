



#check Or.rec

#check Eq.trans

#check Trans

/-

How to support by-cases and calc style transitivity assertions.


by-cases:
- delab, expecting `Or.rec ... (Classsical.em _)` (check this)
- store Prop that's being disjoint on in PI, keeping track of fvars and their types
  (can generalisation API with its mvar types be re-used here ?)
- generalize PI
- for each elem in PI, consider an `Or.rec ... (Classsical.em _)` with it
  as entry for the prop, then bounded by the additional fvars
- treat this as thm, which will be scored via goal and hyps as others

-/
