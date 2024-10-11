
import LeanGrow.F.Data.CExpr.Types


#check 1

inductive NodeExpr where
| ofNode (i : Nat)
| ofCExpr (c : CExpr)
deriving Inhabited, Repr, BEq



def CExpr.ReduceMatchAssign (l r : CExpr) : Option (List (Nat × NodeExpr)) :=
  sorry


/-
Add stuff to CExpr

- **beta** constructor that wraps two CExpr, one beta-reduced and the other not. When matching at that constructor, try to match with both options.

- **zeta** constructor shoould be like beta

- **nabla** should be wraped around constants (technically als lambdas ?!?) that have a function type. When matching at nabla constructor, inspect if other is nabla expanded ?

- **delta** ; to avoid requiring a getEnv Monad, make a cache with constants ; distinguish axioms, constructors, recursors, and delta-expandable constants ; When matching, replace constant by valueat try to match with it ; note te value should already be in a CExpr format with all other reduction constructors

- **iota** ; probably best to use a single constructor for recursor applications rather then an application ; When matching on a iota node, if no direct match, check if main arg is a constructor (head is a constructor) and which one, and select branch accordingly, and try to match on it.

- **rw** experiment with a constructor that is meant for search-time only, that indicates multiple options for a cexpr, depending on rewrites found durring search

-/
