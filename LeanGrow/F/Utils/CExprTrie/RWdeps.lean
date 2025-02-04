
import LeanGrow.F.Utils.CExprTrie.Types
import Lean
import LeanGrow.F.Data.CExpr.API

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


def getHeadPosPriorArgs (odirs : List oDirs) (ce : CExpr) : Nat × CExpr × List (CExpr) × List CExpr :=
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
  ((pos-1),H,Args,baseCtx)


def testExpr : CExpr :=
  .lam `n
    (.const `Nat [])
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
  depsBv : List Nat
  depsPos : List Nat
deriving Inhabited, Repr, BEq


def build_DepDag_ofType (type : CExpr) (init : Nat) : DepDagNode × List DepDagNode :=
  let rec skipToInit : CExpr → Nat → CExpr
    | .forallE _ _ b _, n+1 => skipToInit b n
    | x, 0 => x
    | _,_ => .failed
  let rT := skipToInit type init
  let rec main (dd : List DepDagNode) (depBvs : List Nat) (depth : Nat) : CExpr → DepDagNode × List DepDagNode
    | .forallE _ t b _ =>
        let bvs := getRelBvInd t depBvs depth
        let off := init + depth
        let pos := bvs.map (off - · - 1)
        let next_depBvs := if bvs.isEmpty then (depBvs.map Nat.succ) else 0 :: (depBvs.map Nat.succ)
        let next_dd := if bvs.isEmpty then dd else ⟨off, t, bvs, pos⟩ :: dd
        main next_dd next_depBvs (depth+1) b
    | h => -- head reached
    /- Actually, holy fuck, the output type may change when we rewrite an input,
    which may incure further dependencies !!! (if the output is itself an input
    to some application) Hence the name dtt Hell
    -/
        let bvs := getRelBvInd h depBvs depth
        let off := init + depth
        let pos := bvs.map (off - · - 1)
        (⟨off, h, bvs, pos⟩, dd)
  main [] [0] 1 rT

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
