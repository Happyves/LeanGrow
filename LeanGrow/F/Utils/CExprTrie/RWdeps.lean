
import LeanGrow.F.Utils.CExprTrie.Types
import Lean
import LeanGrow.F.Data.CExpr.API
import Mathlib.Data.List.Sort
import LeanGrow.F.Data.CExpr.ReduceInferMuggle.Reduce

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
  In any case, we use this information to determine which arguments' types
  depend on the one we want to rewrite. After that, we should do the same
  for each of the dependencies, to get their dependencies. Finally, we check
  if there are dependencies of 3rd order, in which case we just don't allow
  the rewrite, for the moment.

- λ and ∀ case:
  A priori no issue if we rewrite in body, so only laa and ala in odirs.
  If we rewrite in binding type, affects future binding types, and the
  arguements at the corresponding positions *outside/above* that λ/∀.
  How abount we just make these rewrites illegal for now ?

- let case :
  Does it even ever show up ? Prohibit for now

-/


def getFromOdirs (odirs : List oDirs) (ce : CExpr) : CExpr × List CExpr :=
  let rec go (bvarCtx : List CExpr) : List oDirs → CExpr → CExpr × List CExpr
    | .apf :: od, .app f _ => go bvarCtx od f
    | .apa :: od, .app _ a => go bvarCtx od a
    | .laf :: od, .lam _ f _ _ => go bvarCtx od f
    | .laa :: od, .lam _ f a _ => go (f :: bvarCtx) od a
    | .alf :: od, .forallE _ f _ _ => go bvarCtx od f
    | .ala :: od, .forallE _ f a _ => go (f :: bvarCtx) od a
    | .lef :: od, .letE _ f _ _ _ => go (bvarCtx) od f
    | .lea :: od, .letE _ _ a _ _ => go (bvarCtx) od a
    | .lez :: od, .letE _ f _ z _ => go (f :: bvarCtx) od z
    | .pro _ _ :: od, .proj _ _ e => go bvarCtx od e
    | [], ce => (ce, bvarCtx)
    | _, _ => (.failed, [])
  go [] odirs ce


def getHeadPosPriorArgs (odirs : List oDirs) (ce : CExpr) : Nat × CExpr × CExpr × List (CExpr) × List CExpr × List oDirs :=
  let od := odirs.tailD []
  --dbg_trace s!"od : {repr od}"
  let rec appDirsCount (c : Nat) : List oDirs → Nat × List oDirs
    | .apf :: more => appDirsCount (c+1) more
    | x :: more => (c,x :: more)
    | [] => (c,[])
  let (priorArgsNum, appDirs) := appDirsCount 0 od
  --dbg_trace s!"(priorArgsNum, appDirs) : {repr (priorArgsNum, appDirs)}"
  let (base, baseCtx) := getFromOdirs appDirs.reverse ce
  --dbg_trace s!"(base, baseCtx) : {repr (base, baseCtx)}"
  let rec fst (as : List CExpr) : Nat → CExpr → CExpr × List CExpr
    | 0, ce => (ce, as)
    | n+1, .app f a => fst (a :: as) n f
    | _,_ => (.failed,[])
  let (hf,Args) := fst [] priorArgsNum base
  --dbg_trace s!"(hf,Args) : {repr (hf,Args)}"
  let rec snd (c : Nat) : CExpr → Nat × CExpr
    | .app f _ => snd (c+1) f
    | x => (c,x)
  let (pos,H) := snd 0 hf
  --dbg_trace s!"(pos,H) : {repr (pos,H)}"
  ((pos-1),H, base, Args,baseCtx, appDirs)
  -- base will be needed for the motive, so we recycle it ; same with Appdirs


def testExpr : CExpr :=
  .lam `n
    (.const `Int [])
    (.app
      (.app
        (.app
          (.app
            (.const `PSigma.mk [])
            (.const `Nat [])
            )
          (.const `Fin [])
          )
        (.const `fourtytwo [])
        )
      (.const `someFin42 [])
      )
  .default

#check PSigma.mk
#check Fin


#eval getHeadPosPriorArgs [.apa,.apf,.apf,.apf,.laa] testExpr
#eval getHeadPosPriorArgs [.apa,.apf,.laa] testExpr


-- inductive DepTree where
-- | leaf (idx : Nat) (deps : List Nat) | node (idx : Nat) (deps : List Nat) (kids : List DepTree)
-- deriving Inhabited, Repr, BEq


partial def getRelBvInd (type : CExpr) (depBvs : List Nat) (depth : Nat) : List Nat :=
  let rec go (done : List Nat) : List (CExpr × Nat) → List Nat
    | [] => done
    | (.app f a, d) :: m => go done ((f,d) :: (a,d) :: m)
    | (.lam _ f a _, d) :: m => go done ((f,d) :: (a,d+1) :: m)
    | (.forallE _ f a _, d) :: m => go done ((f,d) :: (a,d+1) :: m)
    | (.letE _ f a z _, d) :: m => go done ((f,d) :: (a,d) :: (z,d+1) :: m)
    | (.proj _ _ f , d) :: m => go done ((f,d) :: m)
    | (.bvar i, d) :: m =>
        let cal := i - d
        if (depth > cal) && (i ≥ d) && (depBvs.contains cal)
        then go (cal :: done) m
        else go done m
    | _ :: m => go done m
  go [] [(type, 0)]

structure DepDagNode where
  pos : Nat
  type : CExpr
  ctx : List CExpr
  depsBv : List Nat
  depsPos : List Nat
deriving Inhabited, Repr, BEq


--#exit

-- we stoped considering a bvarcontext since we gave up on rw under binders
def build_DepDag_ofType (type : CExpr) (init : Nat) : DepDagNode × List DepDagNode :=
  let rec skipToInit (bvs : List CExpr) : CExpr → Nat → CExpr × List CExpr
    | .forallE _ t b _, n+1 => skipToInit (t :: bvs) b n
    | x, 0 => (x, bvs)
    | _,_ => (.failed, [])
  let (rT,bvPreArgs) := skipToInit [] type init
  let rec main (dd : List DepDagNode) (bvc : List CExpr) (depBvs : List Nat) (depth : Nat) : CExpr → DepDagNode × List DepDagNode
    | .forallE _ t b _ =>
        let bvs := (getRelBvInd t depBvs depth).eraseDups.insertionSort (· ≥ · ) -- order important for future
        let off := init + depth
        let pos := bvs.map (off - · - 1) -- important to keep order
        let next_depBvs := if bvs.isEmpty then (depBvs.map Nat.succ) else 0 :: (depBvs.map Nat.succ)
        let next_dd := if bvs.isEmpty then dd else ⟨off, t, bvc, bvs, pos⟩ :: dd
        main next_dd (t :: bvc) next_depBvs (depth+1) b
    | h => -- head reached
    /- Actually, holy fuck, the output type may change when we rewrite an input,
    which may incure further dependencies !!! (if the output is itself an input
    to some application) Hence the name dtt Hell
    -/
        let bvs := (getRelBvInd h depBvs depth).eraseDups.insertionSort (· ≥ · )
        let off := init + depth
        let pos := bvs.map (off - · - 1)
        (⟨off, h, bvc, bvs, pos⟩, dd)
  main [] bvPreArgs [0] 1 rT



open Meta Elab Term

elab "test1" n:num t:term : command => Command.liftTermElabM do
  let N := n.getNat
  let et ← elabTermAndSynthesize t .none
  let cet := et.toCExprF
  let res := build_DepDag_ofType cet N
  IO.println (repr res)

--#exit

test1 5 (∀ {α : Sort _} {β γ: α → Sort _} {δ : (a : α) → β a → γ a → Sort _}
  {a : α} {b : β a} {c : γ a} {d : δ a b c}
  {motive : (w : α) → (x : β w) → (y : γ w) → (z : δ w x y) →  Sort _}, motive a b c d)
  -- 5 refers to a rewrite of `a`
  -- Context: the above could be the type of SomeRec and we want to rw 2+2=4 in
  -- SomeRec Nat Fin Fin (fun _ _ _ => Nat) (2+2) 1 1 42 (fun _ _ _ _ => ())

test1 6 (∀ {α : Sort _} {β γ: α → Sort _} {δ : (a : α) → β a → γ a → Sort _}
  {a : α} {b : β a} {c : γ a} {d : δ a b c}
  {motive : (w : α) → (x : β w) → (y : γ w) → (z : δ w x y) →  Sort _}, motive a b c d)
  -- 6 refers to a erwrite of `b`

test1 0 (∀ (n : Nat) (x : Fin n) (y : Fin (n+2)), x.val + y.val = 42)
test1 1 (∀ (n : Nat) (x : Fin n) (y : Fin (n+2)), x.val + y.val = 42)
test1 2 (∀ (n : Nat) (x : Fin n) (y : Fin (n+2)), x.val + y.val = 42)


/-
A rewrite in an application that has an output-type that depends on that argument shouldn't
be that much of a problem though. In the case where the ouptut is a argument to a further application,
we make a first rewrite showing equality of the initial application and its version with the initial
rewrite. Then, we use this equality and try to perform the rewrite in the upper application.
We should prohibit rewrites when the head of the application depends on the rewrite, and it's an
input to further rewrites. Can explored ths in further research

Example of annoying dependence: we have
- F : (n : Nat) → Fin n
- G : (x : Fin 42) → Nat
and we want to rewrite 42 = 2*21 in G (F 42)
```
example (F : (n : Nat) → Fin n) (G : (x : Fin 42) → Nat) (h : G (F 42) = 37) : True := by
  have eq : 42 = 2*21 := rfl
  rw [eq] at h -- fails
```
Example of a dependence we want to handle:
- F : (n : Nat) → Fin n → Nat
- A B : List Unit
- eq : A = B
- h : 2 < A.length
and we want to rewite eq in F A.length ⟨2,h⟩

-/

#check HEq.ndrec
#check HEq.subst

noncomputable
def HEq.cast {p : (T : Sort _) → T → Sort _} {a : α} {b : β} (h₁ : HEq a b) (h₂ : p α a) : p β b :=
  HEq.ndrecOn h₁ h₂



--#exit

/-
There are 3 "versions" of rewriting:
- conversion : we want to unify two terms, that share a motive
  This should be solved with the PSigma methods with *known* motive args
  In search, this will be interpreted as a backstep with remain goals the HEqs
- congruence : the goal is a an (h)equality of two terms that share a motive
  Same as with conversion (the args are known), but the actual motive will
  be an (h)equality and the init-motive.arg will be refl
  Again, in search, this will be a backstep
- Forward/Backward steps : here, we want to use a single equality that is
  the result of some lemma, on a pattern somewhere.
  Here, we want to use cast and cast_heq on the dependent terms of the pattern,
  so that the only remaining goals/args are those of the used theorem

-/


private def subsAndBump (bid : Nat) (e : CExpr) : CExpr :=
  let rec go (d : Nat) : CExpr → CExpr
    | .app f a => .app (go d f) (go d a)
    | .lam n t b i => .lam n (go d t) (go (d+1) b) i
    | .forallE n t b i => .forallE n (go d t) (go (d+1) b) i
    | .letE n t b z i => .letE n (go d t) (go d b) (go (d+1) z) i
    | .proj n i e => .proj n i (go d e)
    | .bvar i =>
        if i == bid
        then .bvar d
        else
          if i < d
          then .bvar i
          else .bvar (i+1)
    | x => x
  go 0 e


--#exit

/-
Random important note.
Since we allow for the pattern to occure under binders, the types we consider
may refer to loose bvars refering to these bindings.
This may cause prblems at the nested-rws-due-to-dep-output-type ...
-/

-- Ok, so from now on I assume we're not rewriting in or under binders
-- since this causes issues everywhere, and shouldn't appear in our
-- search procedure anyway ?


/-- Should produce the α, β, γ of our tests -/
def DepDagNode.factorType (fctx : FixCtx) (dn : DepDagNode) : CExpr :=
  let rec go (sofar : CExpr) : List Nat → CExpr
    | [] => sofar
    | bv :: bvs =>
        let type := CExpr.inferType fctx (dn.ctx.getD bv .failed)
          -- massive bug potential here ; if types depend on each other
          -- we must add to fctx ; should be solved in ReduceSmart via bvarCtx
        let next := .lam `grow type (subsAndBump bv sofar) .default
        go next bvs
  go dn.type dn.depsBv
    -- makes use of the order of bvars (greatest first, so that we
    -- follow order of our tests)


#check (default : FixCtx)


elab "test2" n:num t:term : command => Command.liftTermElabM do
  let N := n.getNat
  let et ← elabTermAndSynthesize t .none
  let cet := et.toCExprF
  let (_,nodes) := build_DepDag_ofType cet N
  let res := nodes.map (DepDagNode.factorType default)
  IO.println (repr res)

#check 1

-- test2 1 (∀ (n : Nat) (x : Fin n) (y : Fin (n+2)), x.val + y.val = 42)
-- fails due to the absolte mess that is type inference

/-- Should produce the α, β a, γ a b of our tests
Should be the type of dn.pos -/
def DepDagNode.factoredType (fctx : FixCtx) (dn : DepDagNode) (Args : List CExpr) (init : Nat) : -- Args from getHeadPosPriorArgs
  CExpr :=
    let facto := DepDagNode.factorType fctx dn
    let revRelPos := dn.depsPos.reverse.map (· - init) -- so init was pointless ?
    let relArgs := revRelPos.map (fun n => Args.getD n .failed)
    facto.mkApp relArgs



private def BumpBy (bum : Nat) (e : CExpr) : CExpr :=
  let rec go (d : Nat) : CExpr → CExpr
    | .app f a => .app (go d f) (go d a)
    | .lam n t b i => .lam n (go d t) (go (d+1) b) i
    | .forallE n t b i => .forallE n (go d t) (go (d+1) b) i
    | .letE n t b z i => .letE n (go d t) (go d b) (go (d+1) z) i
    | .proj n i e => .proj n i (go d e)
    | .bvar i =>
        if i < d
        then .bvar i
        else .bvar (i+bum)
    | x => x
  go 0 e

private def AddAt (ds : List oDirs) (p e : CExpr) : CExpr :=
  let rec go : List oDirs → CExpr → CExpr
    | .apf :: m, .app f a => .app (go m f) a
    | .apa :: m, .app f a => .app f (go m a)
    | .laf :: m, .lam n f a i => .lam n (go m f) a i
    | .laa :: m, .lam n f a i => .lam n f (go m a) i
    | .alf :: m, .forallE n f a i => .forallE n (go m f) a i
    | .ala :: m, .forallE n f a i => .forallE n f (go m a) i
    | .lef :: m, .letE n f a z i => .letE n (go m f) a z i
    | .lea :: m, .letE n f a z i => .letE n f (go m a) z i
    | .lez :: m, .letE n f a z i => .letE n f a (go m z) i
    | .pro _ _ :: m, .proj n i e => .proj n i (go m e)
    | [], _ => p
    | _,_ => .failed
  go ds e

private def subsAndBumpHard (revRelPos depPos depBvs : List Nat) (init off : Nat) (e : CExpr) : CExpr :=
  let rec go (d : Nat) : CExpr → CExpr
    | .app f a => .app (go d f) (go d a)
    | .lam n t b i => .lam n (go d t) (go (d+1) b) i
    | .forallE n t b i => .forallE n (go d t) (go (d+1) b) i
    | .letE n t b z i => .letE n (go d t) (go d b) (go (d+1) z) i
    | .proj n i e => .proj n i (go d e)
    | .bvar i =>
        if depBvs.contains  i -- no shift by depth ?
        then
          let i1 := depBvs.indexOf i
          let i2 := (depPos.getD i1 0) - init
          let i3 := revRelPos.indexOf i2
          .bvar i3
        else
          if i < d
          then .bvar i
          else .bvar (i+off)
    | x => x
  go 0 e


/-- Builds (unapplied) the motive
Important: make sure to add the rw node to the `deps` befaore running this-/
def makeMotiveRW (deps : List DepDagNode) (Args : List CExpr) (base : CExpr)
  (appdirs : List oDirs) (ce : CExpr) (init : Nat) : CExpr :=
  let relPos := deps.map (fun x => x.pos - init) -- shift by init was indeed pointless
  let off := deps.length
  let bbase := BumpBy off base -- make room for the λ of the motive
  let (app_res, _) := Args.foldl (fun (sofar,i) x =>
    -- if arg isn't affected by rewrite, leave as is, else replace by bvar refering to λ of motive
    if relPos.contains i
    then
      (.app sofar (.bvar (off - i)), i+1)
    else
      (.app sofar (BumpBy off x), i+1)
    ) (bbase,0)
  let unwrappedMotive := AddAt appdirs -- reverse ?
    app_res ce -- since rewrite occured in application in a pattern, add pattern to motive
  let revRelPos := relPos --.reverse -- actually no
  let (res, _) := deps.foldl (fun (sofar,i,remaining_revRelPos) x =>
    let fixedType := subsAndBumpHard remaining_revRelPos x.depsPos x.depsBv init (off-i) x.type
    -- we bump loose bvars by the number of *remaining* λ to be added
    -- the dependent bvars should be replaced by new ones refering to the
    -- new λ of the motive ; since we expect λs to be in the order of revRelPos
    -- we consider the position the initial bvar corresponded to, and replace it
    -- by the index in the *remaining* dependencies
    -- Probably have to debug the shit out of this
    (.lam `grow fixedType sofar .default, i+1,remaining_revRelPos.tailD [],)
    ) (unwrappedMotive,1,revRelPos)
  res

#check List.indexOf


/-- Builds the motive evaluated in the dependent args. Should be the type of what we
want to rewrite. Important: make sure to add the rw node to the `deps` befaore
running this-/
def makeMotiveRWInstance (deps : List DepDagNode) (Args : List CExpr) (base : CExpr)
  (appdirs : List oDirs) (ce : CExpr) (init : Nat) : CExpr :=
  let lamMot := makeMotiveRW deps Args base appdirs ce init
  deps.foldl (fun sofar x =>
    .app sofar (Args.getD (x.pos - init) .failed)
    ) lamMot


--def buildInterPSigma


/-
Roadmap:
- rw of arg in application with no prior binds : test18
- auto casting and proof_irrel for forward and backwar in test16 and test17
- nested applications : test27 and the one above test19
- rewriting binding types : test28 (may censor case of dependent head, so that we only cast args)
- rewriting under binders via test22_2 and test22, wraped arround others
  rewriting under binders is a big deal, since if we embed the thm and we find a pattern with
  bvars then we can't have that equality as a valid type, as we'd have loose bvars...

Strategy for rw possibly under binders, in possibly nested applications
- Top down ; assumes we know the type correct replacements (ie. with cast and proof_irrel
  for forward and backward steps, and corresponding replacements at conversion/congruence)
- We have to find out the top-most affcted application (recall that we could have a top most
  application, where the rw is in a first arguement and a second once depends on it, and where
  the first could a λ, with body further nested application containing the rw pattern ; basicly,
  I'm saying it can be nested applications and λ ∀ !)
- mini note test18 can also be used when the rw is the head of an application !

For Backward
- factor motive up to first ∀ λ, make Eq.ndrec Backstep and for equality arguement, proceed:
- make Intro Backsteps after Backstep of test22_2/test22, repeated
- do so until we reach top-most affected application
- for affected application, proceed à la test18, where the eq is that of the argument to its
  rewritten one, which will then be a new goal solved by further backsteps
- at binders, test22_2/test22
- at the very end, use thm backstep (mini note ; the unification from pattern search may contain
  loose bvars), so instead reunify, where the gnodes should now be introed-gnodes

For forward:
Same as backstep, but instead of backsteps, let "goal" be bvar, bind thm in a fun, and make it
head of app who's arg will be term of proof of "goal". For ∀ subtasks in test22_2/test22, add fun
and refer and use bvar, since index should be the same !(?!)
Actually, we should be able to do backsteps this way ??

For convert / congr:
Whole other thing ?
- conversion in the context of unification will do two things : conversion rewrites and lnode assignments
- decide whether to try match in the first place: ex, `2.succ` and `x y` will yield `HEq Nat,succ x`
  and `HEq 2 y`, which may be totally meaningless
- we can look through the terms, stopping if subterms ≠, and leaving this as goal. Though, if we want
  to proceed as in test18, we have to figure out the dependencies... Also, we should stop at binders,
  as this will otherwise cause type incorrect recursor applications.
- perhaps "figuring out the dependencies" could work by considering the differences from left to right ;
  the context will be to try to use the schema in test18 ; after we considered the left-most difference,
  say `a` vs `b`, we look for the next ones, and check if their types have form `β a` and `β b` for a β
  to be determined. If the next ones are independent of `a` and `b`, then this could be a second "thread".
  Note that we can still find a β in this case, namely a constant function ! We then proceed like this...
- A criterion on whether to persue the conversion could be the number of matching leaves of the CExpr
  (const, etc) (preferably many), and how many "threads" (in the sense ↑) there are (preferably few).
- A note on conversion à la test18, on reverting :
  we could replace (h : a = b) (H : HEq c = d) by
  (h : a = b) (H : ∀ _ : a = b, Heq c = d) since we can recover
  H h : HEq c = d, and in the subgoal ∀ _ : a = b, Heq c = d we'll
  gain teh equality as hypothesis, without requiring it to have been
  built in forward-context ...
  Actually, in the context where we have a trie of goals, this wouldn't be
  too dramatic: if a back step equired a = b as subgoal, it would be assigned
  to the goals first appearance. The above note allows for easier forward
  steps, though.

Case of RW in binding type
- proceed as above using Eq.ndrec and test22_2/test22 until we arrive at binding type ...
- we'll try to follow scheme test29 ; ie. show euqality of binding types, factor a γ and use test29
  to conclude with the final equality ; as we note in test30, fruther binders with types dependent
  on initial one don't seem to need to be cast ; this seems to be due to the fact that any function
  in the body having them as arg must have also depended on the init binding, so that types make sense ???!?
- don't know what to do with test31 and test32 ; can't be used to show eq, but heq ...
- again that binder may hav been an argument in an application, and we should handle these as in test18


Study takeaways:
- use `pi_congr`, though indirectly via copy, for better maintenance
- 4 cases ; λ, ∀, let, appli
- grow downwards
- cast / proof_irrefl

-/

#check pi_congr

#check DepDagNode.factoredType


/--
goal is to preduce the expr of goals
{f : β e} → {g : γ e} → {h : δ e f g} → HEq b f → HEq c g → HEq d h → motive e f g h
{g : γ a} → {h : δ a f g} → HEq c g → HEq d h → motive a f g h
from test23
-/
def mkRerverted (fctx : FixCtx) (dns : List DepDagNode)
  (motive : CExpr)
  (Args : List CExpr)
  (init : Nat) -- debt
  (split : Nat) -- will be where we split from args to bvars !
  : CExpr :=
  let toRev := dns.drop split
  let UseArgs := Args.take split
  let bvarsForEntryTypes := (List.range (Args.length - split)).reverse
  let ArgsForTypes := (UseArgs) ++ (bvarsForEntryTypes.map (CExpr.bvar))
  let Types := toRev.map (fun dn => dn.factoredType fctx ArgsForTypes init)
  let ArgsForHEqTypes := UseArgs ++ ((bvarsForEntryTypes.map (· + (Args.length - split))).map (CExpr.bvar))
  let TypesForHEq := toRev.map (fun dn => dn.factoredType fctx ArgsForHEqTypes init)
  let stdTypes := toRev.map (fun dn => dn.factoredType fctx Args init)
  let rec mkHeqs (done : List CExpr) : List CExpr → List CExpr → List CExpr → List CExpr
    | fromType :: fTs, fromArg :: fAs, toType :: Tts =>
        -- fix universes in ↓
        let next := .app (.app (.app (.app (.const `HEq []) fromType) fromArg) toType) (.bvar toRev.length) -- ± 1 ?
        -- the bars refering to the argument will all be the same, as the distance in the lambdas
        -- stays the same : we refer to the next arg, but we added an HEq to the binding
        mkHeqs (next :: done) fTs fAs Tts
    | [], [], [] => done
    | _,_,_ => []
  let HEqs := mkHeqs [] stdTypes ArgsForHEqTypes TypesForHEq
  let ArgsForMotive := UseArgs ++ ((bvarsForEntryTypes.map (· + (Args.length - split) + HEqs.length)).map (CExpr.bvar))
  let rec mkAll (head : CExpr) : List CExpr → CExpr
    | [] => head
    | t :: ts => mkAll (.forallE `grow t head .default) ts
  mkAll
    (motive.mkApp ArgsForMotive) --??
    (HEqs ++ Types.reverse) -- no reverse HEqs cause they should as output ?

/--
goal is to preduce the expr of the motive of the Eq.rec
fun e _ => {f : β e} → {g : γ e} → {h : δ e f g} → HEq b f → HEq c g → HEq d h → motive e f g h
fun f _ => {g : γ a} → {h : δ a f g} → HEq c g → HEq d h → motive a f g h
from test23
-/
def mkRervertedAsMotive (fctx : FixCtx) (dns : List DepDagNode)
  (motive : CExpr)
  (Args : List CExpr)
  (init : Nat) -- debt
  (split : Nat) -- will be where we split from args to bvars !
  : CExpr :=
  let toRev := dns.drop split
  let UseArgs := Args.take (split-1)
  let bvarsForEntryTypes := (List.range (Args.length - split)).reverse ++ [((Args.length - split) +1) ]
  -- ↑ the +1 is to skip the = arg of the fun in the motive
  let ArgsForTypes := (UseArgs) ++ (bvarsForEntryTypes.map (CExpr.bvar))
  let Types := toRev.map (fun dn => dn.factoredType fctx ArgsForTypes init)
  let ArgsForHEqTypes := UseArgs ++ ((bvarsForEntryTypes.map (· + (Args.length - split))).map (CExpr.bvar))
  let TypesForHEq := toRev.map (fun dn => dn.factoredType fctx ArgsForHEqTypes init)
  let stdTypes := toRev.map (fun dn => dn.factoredType fctx Args init)
  let rec mkHeqs (done : List CExpr) : List CExpr → List CExpr → List CExpr → List CExpr
    | fromType :: fTs, fromArg :: fAs, toType :: Tts =>
        -- fix universes in ↓
        let next := .app (.app (.app (.app (.const `HEq []) fromType) fromArg) toType) (.bvar toRev.length) -- ± 1 ?
        -- the bars refering to the argument will all be the same, as the distance in the lambdas
        -- stays the same : we refer to the next arg, but we added an HEq to the binding
        mkHeqs (next :: done) fTs fAs Tts
    | [], [], [] => done
    | _,_,_ => []
  let HEqs := mkHeqs [] stdTypes ArgsForHEqTypes TypesForHEq
  let ArgsForMotive := UseArgs ++ ((bvarsForEntryTypes.map (· + (Args.length - split) + HEqs.length)).map (CExpr.bvar))
  let rec mkAll (head : CExpr) : List CExpr → CExpr
    | [] => head
    | t :: ts => mkAll (.forallE `grow t head .default) ts
  let inner := mkAll
    (motive.mkApp ArgsForMotive) --??
    (HEqs ++ Types.reverse) -- no reverse HEqs cause they should as output ?
  let T := (dns.get! split).type
  -- ↓ universes
  let EQ := .app (.app (.app (.const `Eq []) T) (Args.get! split)) (.bvar 0)
  .lam `grow (dns.get! split).type (.lam `grow EQ (inner) .default) .default
