
import LeanGrow.F.Utils.CExprTrie.Types

open Lean

#check 1

/-
After `find_occurences`, odirs are in bottom up order.

- App case :
  head of odirs is .apa ; so it is an argument in an application
  we should then get the head of that application, by following
  the tail of the odirs and then following app heads until we can't.
  We should count how many steps we take until the app head, as this will
  determine the position of the arg in the app. We should also collect
  the prior args of the app along the way, and the posterior ones (the odirs
  should be of for [apa,apf,apf,...,], and the posterior args are reached
  by truncating the previous apf and replacing them by one apa).
  The head can be a lambda, or a bvar/gnode/const, in which case we must
  infer the type, which requires building the expression the pattern was
  found in and processing a bvarCtx etc.
  In any case

-/
