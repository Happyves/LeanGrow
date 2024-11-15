
import LeanGrow.F.Data.CExpr.API
import LeanGrow.F.Utils.RWclassBFS.BFS
import LeanGrow.F.Utils.ExprTrieRW.Types

#check Eq.trans
#check Eq.symm

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

Note that all terms of the class should have the same type. This type should
be infered once and stored with the class, so that we don't recompute it when
needing it for thm-building
-/

open Lean

partial def buildEqThm
  (class_type : CExpr) (class_type_level : Level)
  (class_cexprs : List (Nat × CExpr))
  (base : List ((Nat × Nat) × CExpr)) -- ((index_left, index_right), thm_value)
  (class_graph : BFS.graph)
  (source dest : Nat) :
  CExpr :=
    let path := BFS.bfs source dest class_graph
    let rec mkSymms (done : List ((Nat × Nat) × CExpr)) : List ((Nat × Nat) × Bool) → List ((Nat × Nat) × CExpr)
      | [] => done
      | (edge, d) :: more =>
          match (base.find? (fun x => x.1 == edge)) with
          | .some (_,thm) =>
              if d
              then
                mkSymms ((edge, thm) :: done) more
              else
                match (class_cexprs.find? (fun x => x.1 == edge.1)), (class_cexprs.find? (fun x => x.1 == edge.2)) with
                | .some (_,term_left), .some (_,term_right) =>
                    let sym := CExpr.mkApp (.const `Eq.symm [class_type_level]) [class_type, term_left, term_right, thm]
                    mkSymms ((edge, sym) :: done) more
                | _, _ => []
          | _ => []
    let chain := (mkSymms [] path).reverse
    let rec mkThm : List ((Nat × Nat) × CExpr) → CExpr
      | [] => .failed
      | [(_,thm)] => thm
      | ((a,b), thmL) :: ((_,c),thmR) :: more =>
          match (class_cexprs.find? (fun x => x.1 == a)), (class_cexprs.find? (fun x => x.1 == b)), (class_cexprs.find? (fun x => x.1 == c)) with
          | .some (_,term_a), .some (_,term_b), .some (_,term_c) =>
              let trans := CExpr.mkApp (.const `Eq.trans [class_type_level]) [class_type, term_a, term_b, term_c, thmL, thmR]
              mkThm (((a,c), trans) :: more)
              -- do this more efficiently ? currently, the term of `a` will be queried again in next iter...
          | _,_,_ => .failed
    mkThm chain


structure RWClassData where
  class_type : CExpr
  class_type_level : Level
  class_cexprs : List (Nat × CExpr)
  class_trie : CExprTrie Nat
  base : List ((Nat × Nat) × CExpr)
  class_graph : BFS.graph


#check Nat.add.eq_1

/-
Conceptualization, cause I'm fucking lost:

- Assume we have ltx `n : Nat ; hn : Even (n+0)`

- We wish to add the rewrite option wrt. thm `Nat.add.eq_1 : ∀ (x : Nat), x.add Nat.zero = x`
  This should be stored in a format where on of the versions has left-search-pattern `(.lnode 0) + 0`

- We need a method that will unify (.lnode 0) + 0` with a subpattern of the tree
  corresponding to ltx `n : Nat ; hn : Even (n+0)`

- After unification, there should be propagation, so that we let `.lnode 0` be `n`

- Then, in the cexpr-trie of ltx `n : Nat ; hn : Even (n+0)`, we should add an RW-branch
  at the location of pattern `n+0`. The rw class should contain terms `n+0` and `n`, and
  the thm with embedding info to rewrite one into the other.

- Next, assume we want to apply thm `Even n → Even (n+2)` (say with the concrete value of `n`, not an `lnode`)

- When lookig for `Even n` in the cexpr-trie, we should get an rw-blueprint

- From the blueprint, we want to get a term of type `Even n` !

-/

example {Even : Nat → Prop} (n : Nat) (h : Even (n+0)) {thm : Even n → Even (n+2)} : Even (n+2) :=
  have : Even n := @Eq.ndrec Nat (n+0) Even h n (Nat.add.eq_1 n)
  thm this


/-
Conceptualization 2, cause I'm fucking lost:

- Assume we have ltx `n : Nat ; hn : Even n`

- We wish to add the rewrite option wrt. thm `Nat.succ_sub_one: ∀ (x : Nat), x.succ - 1 = x`
  This should be stored in a format where on of the versions has right-search-pattern `(.lnode 0)`

- After unification and propagation, only the `n` in `Even n` is detected. For some reason,
  I still get confused with he type-term difference and thought `n : Nat` was somehow involved

-/

#check Nat.succ_sub_one
