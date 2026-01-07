

# Plan for Jan-Feb

# W1 (31-4) FFI & Utils

- FFI (UInt32Array, ArrayProd, etc)
- IndexColType as structure
- Amalgames
- Tracing:
  - Two tracing files, where one turns elabs and macros into no-ops ?
  - Use current system, but make local trace flag in `mtrace` too, so that env extention queried at most once ?
- Learn the new module system
- Utils
  - Expr : use up-down approach from Data for `onAllSubterms` ; keep TR, but don't use it, as it's slower ... ; use `Expr.hasFVars`, `Expr.lt`, `Expr.hash`, pointer eq & co ?
    Also, try to avoid needless `Expr.data` computation.
  - Revert : try to speed up ; version that turns proof-valued-lets to foralls, wrt. reverts of forward steps in search
  - Generalize: same issues as revert ?
- Lake scripts ?


# W2 (5-11) Data ; Sample ; Delab Standard & Rewrite & \t & Subst

LG:
- Do *not* attempty concurrency
- Keep TR versions from Beta, but use rec versions from Alpha, since they should be faster ?? 
- Rudimentary wall-clock profiling to compare TR and non-TR ops in test
- Settries: 
  - Biggest rewrite of the 3 Datas, start with it
  - Use one PaIn for siblings, real settrie with lists of Nats, so that we only query one settrie per generation
  - Fix aweful build process for path indices
- Path indexes:
  - perf: use a map of PaIns, with keys beeing the spines. For example, an app of 3 args and constant head c, a forall, etc.
    This should improve efficiency of queries. Note that "naive mode" will then not be required anymore in this case: also,
    regular query benefits of a second version with no naive mode, since naive mode is never left, and re-querying it is wasteful.
  - After deinifing PaIn.ppS, make it a high priority Repr instance


Djv Core:
- Delta defs and theorems, unless their value is too large ?
- Otherwise, simply discard samples that would require non-lib objects
- better management of haves (if appear once, inline ; or do both inline and no inline ...)


Djv Parse:
- Standard & Rewrite & \t & Subst




# W3 (12-18) Cashing ; Sample ; Delab Induction & Match

LG:
- Support simplifier status
- As exemplified in `dif_pos`, an instance can be given as a regular (here, implicit) arguement, 
  so we have to be more carefule in the preprocess step.
- Make sure `id` is never entered as thm/decl ! Generalise this.
- Add option to include theorems from extentions, such as the simp extention.
- Take note of meta-data, for example if its a ctor, as we may use this for scoring, or an eq-theorem wich acts as a simplifier.
- Loading should enable name actions so that functional induction theorems are in env.
- Theorems who's types are structures : add projections as thms


Djv Core:
- Hang in there!

Djv Parse:
- Induction & Match


# W4 (19-25) Core ; DéjàVue Codes ; Delab Simp

LG:
- Embedding:
  - Skip proofs and instances in rewrite query
  - Optimize forward queries ?
  - Don't attempt forward rewrites ; too time consuming for too little impact
- Rewriting:
  - All binders should be fvars in subgoals ; this should imply no skipping binders in the proofterm, 
    unless there are no subgoals to begin with, in which case the current version is efficient.
  - Keep track of queried Expr sub-expr pointers ; record if no matches, and skip
    subexpressions if encountered again ; maybe even maintain a cache accross queries !
  - Make version that doesn't make rewrites of binding types.
  - refer to revert tests : we should add deps for reverts at rw/induction
- Induction:
  - Try to speed up ?
  - Elab-elim inductions should detect constroturs of recursed type (ex: Fin.mk) ?
  - refer to revert tests : we should add deps for reverts at rw/induction



Djv Core:
- Hang in there!

Djv Parse:
- Delab Simp


# W5 (26-1) Search & Frontend ; Generalize & Denoise ; Delab Calc

LG:
- Consider LLM stuff here too, for its influence on IntroTrees and Backtrees and so on
- Abort when indices (id_gen_ ...) would overflow due to UInt32 or reset them
- Array representation of Introtree (kids via entry containing indices of kids) ; efficient if we don't delete nodes, which is the case
- Allow induction on hyp for goals that are Types. Else `Exists f : Nat -> Nat, ...` won't be able
  to try a recursive function (we expect to try induction on `Nat` with the introed `Nat`)
- For backsteps, if we can tell before full integration (so also unification of subgoals) that
  all hyps are filled in, automatically add it as step to take. This should avoid the akward
  situation from tests where oneliners remain candidates and aren't taken.
- For rewrites at goals that are eqs, consider the rewritten subgoal, and look for similarity
  in a way that allows us to close with refl if the sides are defeq, and if not, gives a
  similarity score ? This reqires a minimum of integration for each candidate though ...
- Give higher score to constructors, or at least, make it a separate score field in the 
  search configurations ...
- Do not allow rewrites under binders of parameters of Prop-valued inductive types or structures
  (example: Exists, ListP.Pairwise ) since we expect constructors or induction to be used, so
  that we'd duplicate rewrites, similar to how they're duplicated by rewriting under \all goals
- When selecting best batch, find system that prevents best batch being made of many different
  applications of the same theorem, when they many have the same score due to the way candidates are stored. Maybe if we see the same pair of goal-index and theorem in the batch too often, ignore further appearances in candidtes and take something else ?
  Or do the oppiste : add all goal-index and theorem pairs with multiple occurences as a single addition, 
  so that the batch size may actually be greater. The worry is that different rewrites will be scored the 
  same, and only some of them will make it inot the best batch, despite all having same score ... but
  then, wouldn't they enter it at some next iteration anyway ??
- Consider adding grind to the tactic support, maybe even as only tactic support
- make non-obvious induction (say, Nat but not Or & Subtype ...) a configurable option since its an absolute
  performance crusher ... or allow it in first iterations only or have its score decrease with iters ... 
- Find system where we check if goal is already there, in the same introtree path to root
  and do not expand that goal (don't query candidates), but still consider it for unification,
  so that when the first occurence of the goal gets solved, it will be added to the forward
  context, and will then immediately unify with the duplicate goal
  Maybe add Expr-hashsets to IntroTree ? New ctor for Backtree "locked" ?
- Forw candidtes are printed in a way so that we sometimes see `Eq.ndrec` ... maybe this is
  due to a getAppFn ...
- The current synth instance situation is an incorrect patch.
  The plan is to locate synths (embedBackProcess in EmbedProcessBack and
  embedForwRWProcess in EmbedProcessForwRW and embedForwIncludePostProcess in
  EmbedProcessForwAPI and in StructuralInd (grep it)) and locate where they
  come into action (addBackCandidate in SelcetCore and addForwCandOfStdStep and
  addForwCandOfRW in Forward).
  We should then update the former by letting them access the introtree, target ids
  and uginds, so that we can determine the right context.
  Finally, to get the right LocalInstances for synth. Any approach based on filtering
  is going to take increasing size, as the expect teh LocalInstances to grow a lot...
  So local instances should be incorporated to the introtree/backtree ...
  Also, the `onAllSubterms` functions and all others that produce workers should get rid
  of worker-local-instances immediately after their use. To ensure linear use, maybe we
  can note LocalInstances's Arrays size before the `onAllSubterms` stuff, then `Array.take`
  on its output to get the original. This assumes `onAllSubterms` doesn't create g/u/tnodes,
  but only workers
- Add initial phase for normalisation, unfolding and generalisation:
  Note wrt \d, maybe don't make different branches, but different searches entirely, that we launsh
  wwhen the initial one has failed ? Avoids falsification of backtree based scores
  - Normalising: whnf everything in the initial search state ? Maybe induct on all non-recusive-structure-typed
    fvars, only if we implemented detecting ctors in elab-elim-induction ?
  - Unfolding : make branches from initial goal in backstate in which we unfold constants,
    as we don't really expect to unfold any further constants unless those at right reducibility
    durring whnf, and those that have eq_def-theorems ; don't unfold proofs and instances of course.
  - Generalisation: make branche from initial goal in backstate in which we generalise litterals ;
    maybe also generalise function applicaitons that are Type-typed ? (We can do both, one after the other)


Djv Core:
- Generalize : 
 - Generalize proofs by defaut, but not in the top branch
 - Version where ratios may change depending on the depth the brach/subexpressions
 - For score add different generalisations (corresponding to different ratios, for example) from same sample
   to scoring-structures, possibly with different scores 
 


Djv Parse:
- Delab Calc


# W6 (2-8) Search & CallLLM ; Conveyorbelt & Query ; Delab Congr

LG:
- Add support and special score for declarations from the same file as the query

Djv Core:
- Forward, Backward, Subexpressions
- Expr as keys & Thms as keys
- Idea for Or.rec &co


Djv Parse:
- Delab Congr

# W7 (9-15) Search & Heuristic ; Conveyorbelt & Query ; Delab Misc

LG:
- Hang in there!

Djv Core:
- DéjàVue Codes

Djv Parse:
- Prohibiters for linarith, ring, grind, etc.

# W8 (16-22) Debug

Hang in there!

