
import LeanGrow.F.Utils.ExprTrieRW.Query

#check 1


/-
The idea is that at unification-finding, when encountering an none-lnode,
we'd like to consider the set of cexpr that could be assihned to the lnode.
We'll then prune it by considering the type of that none-lnode, and launshing
unification-finding queries for that type in the types of the terms in the
subtree.

-/


/-
Idea:

In a first phase, do unification as follows. On first query, build all
possible unifying types, ie. get a list of types that unify with the query,
and for each which lnode was assigned to what. Discard all rw-infos, but
be sure to build all combinaitons.
Then, propagate by uni-queriying for lnode assignements, and prune tentative
embeddings if one query yields nil.
At the end of the process, we should know have some structure that collects
all possibilities for a coherent collection of types of none-lnodes.
Only then do we build the terms of these types, up to rws, with `find?`
and `buildRWofBluePrint_3`.

-/
