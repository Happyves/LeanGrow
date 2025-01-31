
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


-- #eval getHeadPosPriorArgs [.apa,.apf,.apf,.apf,.laa] testExpr
-- #eval getHeadPosPriorArgs [.apa,.apf,.laa] testExpr
