
import LeanGrow.F.Data.CExpr.API

open Lean


#check Nat.le.rec

#check List.Mem.rec


/-
Random thoughts :

Treat in induction as backstep (`rec`, `match_1` and `induct`), where we have
to build a motive instead of trying to infer it.
Durring search, we should therefore not treat it in any special way ? Probably
not so good for elementary proofs that aren't similar to sampled ones !
For example if we define new inductive types of recursive functions.

Should we take the opportunity to trigger `.eq_1` rewrites ?

Thinking about adding an mdata constructor that adds flags like isProof or isRec
(or both, for Nat.le typed terms for example) to terms and subterms wrt. their
type. This should make the search for motives more efficient, as we don't have to
query the type of the subterms constantly, but can read its properties from mdata.
Don't know how this will interact with rewriting...
isProof could then be used in unification, and isRec/isMatch when searching a term
for factoring it ; mdata should be added when translating Expr to CExpr, by querying
types of term and subterms, and should be maintained durring operations.
Example of `fun n : Nat => n` that won't be an isRec, but `(fun n : Nat => n) 42` should
be, and we only find out after reduction. Actually, `Nat.add n m` won't be flaged as isRec,
and doesn't reduce. We can add isRecHeaded as flag ?

Reverting works as follows : we consider a gnode and all its dependecies (downward,
ie. all other gnodes that depend on it ; might be synced with rankings ?) ; assume the goal depends on the gnode.
We then add a new goal G that is a ∀ of the gnode and its dependencies, on top of the
current goal, with gnode to bvar abstactions, and solve the initial goal as the application
of G with the gnodes from ltx in the same order we abstracted them. We can handle this with
the `ofRW` BackType of Mark 7, since the effect of assembly will be the same: the preamble
should be `fun x => x gnode1 gnode2 ...`, and it should have 1 argument, which is the goal
will the ∀ abstractions. This should be done for lnodes too : a priori, we treat them the same
as gnodes (ie. add them as args as above) ; they should be replace by their assigned value
after assembly ; there is a twist though : we should prehaps only
revert those who's type doesn't contain lnodes, since otherwise we won't want to intro them afterwards
as this breaks the fact that we have no lnodes in ltx.

So the ansatz for applying recusors as backsteps (and this generalises to other thms) is that we'll
have an application of lnodes with lnode head as goal of thm. We should get the types of the lnodes
arguments, and look for such typed subterms in the actual target. We can then factor according to
these subterms (also, emtpy factor `fun _ => motive` works, in particular for non-dependence,
for example `Nat.le.rec` with a motive that make no use of ≤), to get the motive, and embed as
usual from there.
Note that embedding factors may contain dependecies (ex: t in Nat.le.rec depends on n and a), and
and that we should do some reverting for these terms.

-/


/-- Should also be needed if we have a smart way of deriving deps :
if embedding value isn't gnode but expression with gnodes-/
partial def CExpr.getGNodesDepsF (E : CExpr) : List Nat :=
  let rec go (done : List Nat) : List CExpr → List Nat
  | [] => done
  | nx :: L =>
        match nx with
        | .gnode i _ => go (i :: done) L
        | .app f a => go done (f :: a :: L)
        | .lam _ t b _ => go done (t :: b :: L)
        | .forallE _ t b _ => go done (t :: b :: L)
        | .letE _ t v b _ => go done (t :: v :: b :: L)
        | .proj _ _ b => go done (b :: L)
        | _ => go done L
  go [] [E]
