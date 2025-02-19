
import LeanGrow.F.Data.CExpr.API
import LeanGrow.F.Utils.List
import Mathlib.Data.List.Sort
import LeanGrow.F.Prototypes.MarkSeven.trTypes
import LeanGrow.F.Data.Unification.EmbedGoalWInferWUnis



open Lean


#check Nat.le.rec

#check List.Mem.rec

--#exit

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
Or maybe we should move flags durring whnf/reduction ?


Don't induct on bvars, the recursor applicaiton won't be type correct.

Reverting works as follows : we consider a gnode and all its dependecies (downward,
ie. all other gnodes that depend on it ; might be synced with rankings ?) ; assume the goal depends on the gnode.
We then add a new goal G that is a ∀ of the gnode and its dependencies, on top of the
current goal, with gnode to bvar abstactions, and solve the initial goal as the application
of G with the gnodes from ltx in the same order we abstracted them. We can handle this with
the `ofRW` BackType of Mark 7, since the effect of assembly will be the same: the preamble
should be `fun x => x gnode1 gnode2 ...`, and it should have 1 argument, which is the goal
will the ∀ abstractions. This should be done for lnodes too : a priori, we treat them the same
as gnodes (ie. add them as args as above) ; they should be replace by their assigned value
after assembly ; there is a twist though : we should prehaps only revert those whose type doesn't
contain lnodes, since otherwise we won't want to intro them afterwards
as this breaks the fact that we have no lnodes in ltx. Actually, only revert those which don't have
dependence-descendents, as we would have to revert them ???
This should be considered even if we induct on gnodes, but the motive would contains lnodes !
Actually, we won't introduce lnodes to ltx if we revert all lnodes (and their dependencies)
that are contained in the motive.

So the ansatz for applying recusors as backsteps (and this generalises to other thms) is that we'll
have an application of lnodes with lnode head as goal of thm. We should get the types of the lnodes
arguments, and look for such typed subterms in the actual target. We can then factor according to
these subterms (also, emtpy factor `fun _ => motive` works, in particular for non-dependence,
for example `Nat.le.rec` with a motive that make no use of ≤), to get the motive, and embed as
usual from there.
Note that embedding factors may contain dependecies (ex: t in Nat.le.rec depends on n and a), and
and that we should do some reverting for these terms.

-/

--#exit

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


inductive LoG where
| ofG (_ : Nat) | ofL (tag : Nat) (pos : Nat)
deriving Inhabited, Repr, BEq

/-- Should also be needed if we have a smart way of deriving deps :
if embedding value isn't l/gnode but expression with l/gnodes ;
IMPORTANT: will only consider taged lnodes-/
partial def CExpr.getLGNodesDepsF (E : CExpr) : List LoG :=
  let rec go (done : List LoG) : List CExpr → List LoG
  | [] => done
  | nx :: L =>
        match nx with
        | .gnode i _ => go (.ofG i :: done) L
        | .lnode p _ (.some t) => go (.ofL t p :: done) L
        | .app f a => go done (f :: a :: L)
        | .lam _ t b _ => go done (t :: b :: L)
        | .forallE _ t b _ => go done (t :: b :: L)
        | .letE _ t v b _ => go done (t :: v :: b :: L)
        | .proj _ _ b => go done (b :: L)
        | _ => go done L
  go [] [E]


partial def CExpr.getDepsLtx (ltx : List (Nat × CExpr)) : List (Nat × List Nat × List Nat) :=
      let rec go (deps : List (Nat × List Nat × List Nat)) : List (Nat × CExpr) → List (Nat × List Nat × List Nat)
            | [] => deps
            | (idx,type) :: xs =>
                  let d := type.getGNodesDepsF
                  let (ndeps,rest) := deps.foldl (fun (sofar,rest) (i,kids,P) =>
                        if rest.contains i then ((i,idx :: kids,P) :: sofar, rest.erase i) else ((i,kids,P) :: sofar, rest)
                        ) ([], d)
                  let restWParents := rest.foldl (fun sofar n =>
                        match ltx.find? (fun y => y.1 == n) with
                        | .some (_,T) => (n,T.getGNodesDepsF) :: sofar
                        | _ => sofar -- shouldn't
                        ) []
                  go ((idx, [], d) :: ((restWParents.map (fun (x,t) => (x,[idx],t))) ++ ndeps)) xs
      go [] ltx

/-
In  ↑↓, the dependent gnodes may be from children in other nodes of the IntroTree !
Since we consider dependecies in the context of a specific goal, things are as follows:
If we want to revert gnodes wrt. a goal, we cosider the nodes in the IntroTree
*on the path from the root to associated to that goal*.
So perhaps each node should have a `List (Nat × List Nat)` collecting info on dependecies,
that consideres all gnodes among the ancestor nodes and itself, and considers at children
only gnodes in that path as well.
-/

partial def CExpr.getDepsLtxOnline (deps : List (Nat × List Nat × List Nat))
      (newIdx : Nat) (newType : CExpr) : List (Nat × List Nat × List Nat) :=
      let d := newType.getGNodesDepsF
      let update := deps.foldl (fun sofar (i,kids,parents) =>
            if d.contains i then (i,newIdx :: kids,parents) :: sofar else (i,kids,parents) :: sofar
            ) []
      (newIdx, [], d) :: update

/-
For IntroTrees,nothing changes
-/

--#exit

partial def makeRevertOrderingForGnodes (deps : List (Nat × List Nat × List Nat)) (start : Nat) : List Nat :=
      let rec go (frontier : List Nat) (sofar : List Nat) : List Nat :=
            match frontier with
            | [] => sofar
            | nx :: more =>
                  match deps.find? (fun x => x.1 == nx) with
                  | .none => []
                  | .some (_,kids,_) =>
                        let next := kids.foldl (fun l k => l.orderedInsertOrLeave (· ≤ ·) k) more
                        go next (nx :: sofar)
      go [start] []

partial def makeRevertOrderingForGnodesMany (deps : List (Nat × List Nat × List Nat)) (start : List Nat) : List Nat :=
      let rec go (frontier : List Nat) (sofar : List Nat) : List Nat :=
            match frontier with
            | [] => sofar
            | nx :: more =>
                  match deps.find? (fun x => x.1 == nx) with
                  | .none => []
                  | .some (_,kids,_) =>
                        let next := kids.foldl (fun l k => l.orderedInsertOrLeave (· ≤ ·) k) more
                        go next (nx :: sofar)
      go (start.insertionSort (· ≤ ·)) []

/-
In both ↑, we rely on the fact that a gnode cannot depend on genodes with lower index.
So for situation such as reverting x in `(x : Nat) (y z : Fin x) (h : @Fin.add x y z = 42)`,
h will have higher gnode index, so that when y z and h are in the frontier, y and z will get
added before h.
-/

#check Nat.rec


partial def CExpr.getLNodesDep (E : CExpr) : List (Nat × Nat) :=
  let rec go (done : List (Nat × Nat)) : List CExpr → List (Nat × Nat)
  | [] => done
  | nx :: L =>
        match nx with
        | .lnode p _ (.some t) => go ((t, p) :: done) L
        | .app f a => go done (f :: a :: L)
        | .lam _ t b _ => go done (t :: b :: L)
        | .forallE _ t b _ => go done (t :: b :: L)
        | .letE _ t v b _ => go done (t :: v :: b :: L)
        | .proj _ _ b => go done (b :: L)
        | _ => go done L
  go [] [E]

--#exit

partial def getLnodeDecendents (fctx : FixCtx) (lnodeToRev_WType : List (Nat × Nat × CExpr)) (target_goal_id : Nat) (bt : BackTree) : List (Nat × Nat × CExpr) :=
      let rec skipModeKeep? (id : Nat) : List (Nat × Nat × CExpr) → Bool
            | [] => true
            | (x,_) :: xs => if id == x then false else skipModeKeep? id xs
      let rec inter? (sofar : List (Nat × Nat × CExpr)) : List (Nat × Nat) → Bool
            | [] => false
            | (tag,_) :: more => if (sofar.find? (fun x => x.1 == tag)).isSome then true else inter? sofar more
      let rec go (skipMode : Bool) (sofar : List (Nat × Nat × CExpr)) :  BackTree →  List (Nat × Nat × CExpr)
            | .fail => []
            | .ofAssign _ | .ofUni _ _ => []
            | .ofBack id _ _ gdirs args =>
                  let skip? := if skipMode then skipModeKeep? id sofar else false
                  let next? := gdirs.findIdx? (fun l => l.contains target_goal_id)
                  match next? with
                  | .none => []
                  | .some I =>
                        if skip?
                        then
                              go true sofar (args.get! I)
                        else
                              let (_,next) := args.foldl (fun (i,deps) abt =>
                                    match abt with
                                    | .ofPropa _ _ T _ _ _ | .ofGoal _ T _ _ _ | .ofIntro _  T _ _ _ _ =>
                                          let dep := T.getLNodesDep
                                          if inter? sofar dep
                                          then
                                                (i+1,(id,i,T) :: deps)
                                          else
                                                (i+1,deps)
                                    | .ofAssign V | .ofUni _ V =>
                                          let T := CExpr.inferType fctx V
                                          let dep := T.getLNodesDep
                                          if inter? sofar dep
                                          then
                                                (i+1,(id,i,T) :: deps)
                                          else
                                                (i+1,deps)
                                    | _ => (i+1,deps) -- we shouldn't have ofBack as arg to ofBack ! (this is a constraint we should enforce, not a fact we conjecture)
                                    ) (0,sofar)
                              go false next (args.get! I)
                        /-
                        go over all args, noting position, expecting ofGoal/ofPropa/ofIntro/ofAssign/ofUni
                        for each (at pos p), get the type (t) and check if it has lnodes among those of sofar,
                        and if it does, add entry (id,p,t) to sofar ;
                        Then, recurse on the argument I
                        -/
            | .ofPropa _ gid _ _ _ debt2 | .ofGoal gid _ _ _ debt2 | .ofIntro gid _ _ _ _ debt2 =>
                  if gid == target_goal_id
                  then sofar
                  else go skipMode sofar debt2.head!
                        -- here, we should use fixed gdirs so as recurse on the arg whe the target goal id is
                        -- bug potential : at MarkX, we noted that propagation could lead to index duplication,
                        -- which might be an issue
      go true lnodeToRev_WType bt

#check Array.findIdx?


/--
Here too, we make use of the fact that a gnode can't depend on one with a bigger tag-index.
For the same tag index, we order according to the position in the theorem, which handles dependecies
as side effect.
-/
def orderLNodeDeps (L : List (Nat × Nat × CExpr)) : List (Nat × Nat × CExpr) :=
      let rec insert (tag pos : Nat) (val : CExpr) : List (Nat × Nat × CExpr) → List (Nat × Nat × CExpr)
            | [] => []
            | x :: xs =>
                  match compare tag x.1 with
                  | .lt => (tag,pos,val) :: x :: xs
                  | .eq => if pos < x.2.1 then (tag,pos,val) :: x :: xs else x :: (insert tag pos val xs)
                  | .gt => x :: (insert tag pos val xs)
      let rec go (done : List (Nat × Nat × CExpr)) : List (Nat × Nat × CExpr) → List (Nat × Nat × CExpr)
            | [] => done
            | x :: xs => go (insert x.1 x.2.1 x.2.2 done) xs
      go [] L


/-
Reverting lnodes:
When reverting lnodes in a motive we want to induct on, we walk down the back tree to find dependecies.
We only collect the following dependencies: lnodes that depend on prior ones (starting with those of the
motive) corresponding to backsteps taken up until the current goal. We revert those, as for the goal we're
solving to be a solution, all these lnodes would have to be solved anyway !

**important** bdirs and gdirs are useless for ofPropa ofGoal and ofIntro ! Only makes
sense in ofBack as we know which branch to pick ; actually, they are useful, we just have to make them
List (List Nat) so that entries correpond to gdirs of corresponding arg

-/


#check Nat.le.rec
#check List.Mem.rec


/-
Draft for pipeline:

- for recursor, find pattern via embeddings of the first rec-motive arg (ex: a as Nat in Nat.le.rec)
  in the goal trie. As information, we should retrieve which goals have the pattern, the oDirs to that
  pattern, and the matching pattern ; make a version that only matches for gnodes/lnodes, in case this
  yields too many matches
- we should get the gnodes and lnodes of the matching goal (except for those in the found pattern of course),
  and possibly find the rest of the recursor args (ex: t in Nat.le.rec)
- find dependecies of contained gnodes and lnodes, build the motive with reverts

-/



/--
Should be run on precessed recursor ; since goal (head) is motive x y z,
we get the arguments it depends on, which are the patterns we'll search for
among the goals ; this should be done in preprocess  at stored ?
-/
def MakePatternThmFromGoal (thm : Array EmbedData) (goal : CExpr) : List EmbedData := -- or just get the positions ?
      let rec go (done : List EmbedData) : CExpr → List EmbedData
            | .app f (.lnode p _ .none) => go ((thm.get! p) :: done) f
            | _ => done
      go [] goal

/- The above will give the nodes that are args to the motive. For example, for `Nat.le.rec`,
it will be `t : n.le a` & `a : Nat` (in that order). We should search these patterns among
goals, with the whole recursor as `current` field in `FixCtx`, as we may get assignements
outside of these args (ex: `n` in `t : n.le a`), we should then propagate them among patterns
to embed (ex: if we embed `t : n.le a` , we should get a value for `a`, which we should then
search the location*s* of among the goals that contained `t` ; it will be a bit of a messy if we
get args that have been updated on some of their vals and not on others, ex embed `P x y` first
then `Q x z`...).

It's probably best to separate getting a coherent embedding, and finding all locations of the patterns.

In the context on motives that are constant in some of their args, we should keep trying to embed even
if sinks don't (ex: embed `a` even if `t` didn't)
-/

#check FixCtx

/- Use ↓ on motive -/
def findGnodeDepsExeptOfPattern (ce : CExpr) (patterns : List CExpr) : List (Nat × Nat) :=
      let rec go (done : List (Nat × Nat)) : List CExpr → List (Nat × Nat)
            | [] => done
            | nx :: more =>
                  if patterns.contains nx
                  then []
                  else match nx with
                        | .lnode p _ (.some t) => (go ((t, p) :: done) more)
                        | .app _ _ => sorry
                        -- I wrote this a 100 times
                        | _ => sorry
      go [] [ce]

-- use this on the patterns
#check CExpr.getGNodesDepsF
/-
Actually, if patterns aren't gnodes, then we should revert all hyps that contain that pattern !
One more reason to only induct on gnodes ?!?
-/

-- after ↓
#check makeRevertOrderingForGnodesMany
#check getLnodeDecendents
#check orderLNodeDeps
-- do ↓

def mkMotive (gnodes : List Nat) (lnodes : List (Nat × Nat × CExpr)) (head : CExpr) : CExpr :=
      sorry
      /-
      Todo:
      from motive, to lnodes types, to gnode types, which we should query from ltx, fold:
      abstract gnodes and lvars in the types, replacing occurences with bumped bvars, where
      the unbumped index will correpsond to index of gidx of (tag,pos) in the above arguemnt
      lists ; make λ bindings with these types.
      -/


theorem testInd (n : Nat) (P Q : Nat → Prop) (h : P n) : Q n :=
      (@Nat.rec (fun n => ∀ _ : P n, Q n) (by dsimp ; sorry) (by dsimp ; sorry) n) h

-- Todo next : add gnodes and lnodes back in application

-- don't know where ↓ fits in

/-- After having found and built a goal containing the pattern, we abstarct patterns
by repeatedly running this, to get the motive. In the running example, the first
`valT` will be `n.le a`, and the second will have `a` as val, so that `a` will get
abstracted in the binder type `n.le a` as desired ; actually, its important that
dependence sinks go first for this to work ; in the end, we'll get the motive -/
def abstractAllIn (val valT within : CExpr) : CExpr :=
      let rec go (d : Nat) (ce : CExpr) : CExpr :=
            if ce == val
            then .bvar d
            else  match ce with
                  | .app _ _ => sorry
                  -- I wrote this a 100 times
                  | _ => sorry
                        -- don't forget to bump bvars
      .lam `grow valT (go 0 within) .default


/-
More notes:

- when checking if term is of an inductive type, we should get the head, check that it is a recursor,
  and check that it is fully applied in indices and parameters.


-/
