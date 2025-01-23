
import LeanGrow.F.Prototypes.MarkFour.Frontend
import LeanGrow.F.Prototypes.MarkFour.TestTypes

#check 1




#check 1

example (r : myNat) : myAdd .z (myAdd .z r) = r := by
  grow
  sorry

#check 1


/-
Take-aways :

- separate FixCtx into enivronement info, gnode info and lnode info.
  Forward steps shouldn't depend on lnodes, so that we can make versions of inferType
  and whnf that don't require this info ; then we can make forward steps independent
  of backward ones (the revrese ins't possible because of unification)

- unclear how to doe unification and backsteps in a meaningful way


-/
