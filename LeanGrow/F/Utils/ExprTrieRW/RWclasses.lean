
import LeanGrow.F.Data.CExpr.Types

#check Eq.trans

/-
We assumed rw classes to be refered to by a number (classId).
The class itself would be a list of indexed CExpr, that would all be equal.
There should also be an CExprTrie to quickly query the collection and take
note of rewrites within rewrite classes.
We should collect the theorems that are equalities between expressions.
We could store the equalities as pairs (i,j) where i and j are the indices
of the expressions in the rw class, and store a correspondence between
theorems and these index pairs.
Finding the correct sequence of rewrites correponds to finding a path
via the edges (i,j), which we may walk backwards, a fact we must recollect
so as to wrap the eq-thm in Eq.trans.
-/
