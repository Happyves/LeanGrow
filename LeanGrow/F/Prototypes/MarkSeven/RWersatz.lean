

import LeanGrow.F.Data.Unification.EmbedGoalWInferWUnis
--import LeanGrow.F.Data.Unification.EmbedRawWInferWUnis



#check 1

open Lean

inductive oDirs where
| apf | apa | laf | laa | alf | ala | lef | lea | lez | pro
deriving BEq, Inhabited, Repr


partial def match_pattern_in_goal (fctx : FixCtx)
  (thm_data : Array EmbedData)
  (thm_hyp_num : Nat) (thm_goal real_goal : CExpr) :
  List (CExpr × Array (Option CExpr) × List (Name × Level) × List oDirs) :=
    let rec go (done : List (CExpr × Array (Option CExpr) × List (Name × Level) × List oDirs)) :
      List (CExpr × List oDirs) → List (CExpr × Array (Option CExpr) × List (Name × Level) × List oDirs)
      | [] => done
      | (ce,ds) :: xs =>
          let here? := match_goal fctx thm_data thm_hyp_num thm_goal ce
          match here? with
          | .some (A,L) => go ((ce,A,L,ds) :: done) xs
          | _ =>
              match ce with
              | .app f a => go done ((f,.apf :: ds) :: (a,.apa :: ds) :: xs)
              | .lam _ f a _ => go done ((f,.laf :: ds) :: (a,.laa :: ds) :: xs)
              -- bug potential : we should modify fctx here ; should be fixt when using verison with bvarContext
              | .forallE _ f a _ => go done ((f,.alf :: ds) :: (a,.ala :: ds) :: xs)
              | .letE _ f a z _ => go done ((f,.lef :: ds) :: (a,.lea :: ds) :: (z,.lez :: ds) :: xs)
              | .proj _ _ e => go done ((e,.pro :: ds) :: xs)
              | _ => go done xs
    go [] [(real_goal,[])]


/-- Should be used on the other side of the equality, and on the type-/
def instantiateOther (other : CExpr) (vals : Array (Option CExpr)) : CExpr :=
  let rec go : CExpr → CExpr
    | .app f a => .app (go f) (go a)
    | .lam n f a i => .lam n (go f) (go a) i
    | .forallE n f a i => .forallE n (go f) (go a) i
    | .letE n f a z i => .letE n (go f) (go a) (go z) i
    | .proj n i e => .proj n i (go e)
    | .lnode pos o tag =>
        match vals.get! pos with
        | .some v => v
        | _ => .lnode pos o tag
    | x => x
  go other



/-- Assumes ce is not a subpattern, so that we don't need bvar bumps-/
partial def factorOnDirs (dirs : List oDirs) (ce factType: CExpr) : CExpr :=
  let rec go (d : Nat) : List oDirs → CExpr → CExpr
    | .apf :: m, .app f a => .app (go d m f) a
    | .apa :: m, .app f a => .app f (go d m a)
    | .laf :: m, .lam n f a i => .lam n (go d m f) a i
    | .laa :: m, .lam n f a i => .lam n  f (go d.succ m a) i
    | .alf :: m, .forallE n f a i => .forallE n (go d m f) a i
    | .ala :: m, .forallE n f a i => .forallE n f (go d.succ m a) i
    | .lef :: m, .letE n f a z i => .letE n (go d m f) a z i
    | .lea :: m, .letE n f a z i => .letE n f (go d m a) z i
    | .lez :: m, .letE n f a z i => .letE n f a (go d.succ m z) i
    | .pro :: m, .proj n i e => .proj n i (go d m e)
    | [], _ => .bvar d
    | _,_ => .failed
  let fact := go 0 dirs ce
  .lam `grow factType fact .default

partial def replaceAt (dirs : List oDirs) (ce p: CExpr) : CExpr :=
  let rec go (d : Nat) : List oDirs → CExpr → CExpr -- depth not needed
    | .apf :: m, .app f a => .app (go d m f) a
    | .apa :: m, .app f a => .app f (go d m a)
    | .laf :: m, .lam n f a i => .lam n (go d m f) a i
    | .laa :: m, .lam n f a i => .lam n  f (go d.succ m a) i
    | .alf :: m, .forallE n f a i => .forallE n (go d m f) a i
    | .ala :: m, .forallE n f a i => .forallE n f (go d.succ m a) i
    | .lef :: m, .letE n f a z i => .letE n (go d m f) a z i
    | .lea :: m, .letE n f a z i => .letE n f (go d m a) z i
    | .lez :: m, .letE n f a z i => .letE n f a (go d.succ m z) i
    | .pro :: m, .proj n i e => .proj n i (go d m e)
    | [], _ => p
    | _,_ => .failed
  go 0 dirs ce


def mkRWBackThing (fctx : FixCtx) (dirs : List oDirs) (foundPattern other within : CExpr) : CExpr :=
  let Ptype := CExpr.whnf fctx (CExpr.inferType fctx foundPattern) -- buggggsssss from fctx
  let PtypeT := CExpr.whnf fctx (CExpr.inferType fctx Ptype)
  match PtypeT with
  | .sort u =>
    let motive := factorOnDirs dirs within Ptype
    let motiveT := CExpr.whnf fctx (CExpr.inferType fctx motive)
    match motiveT with
    | .forallE _ _ (.sort v) _ =>
      .lam `nextgoal (replaceAt dirs within other)
        (.lam `eqgoal (.app (.app (.app (.const `Eq [u]) Ptype) other) foundPattern)
          ((CExpr.const `Eq.ndrec [v,u]).mkApp [Ptype,other,motiveT,.bvar 1,foundPattern,.bvar 0])
         .default
        )
      .default
    | _ => .failed
  | _ => .failed


#check Eq.ndrec

#check propext

#check Iff

def mkRWBackThingProp (fctx : FixCtx) (dirs : List oDirs) (foundPattern other within : CExpr) : CExpr :=
    let motive := factorOnDirs dirs within (.sort 1)
    let motiveT := CExpr.whnf fctx (CExpr.inferType fctx motive)
    match motiveT with
    | .forallE _ _ (.sort v) _ =>
      .lam `nextgoal (replaceAt dirs within other)
        (.lam `eqgoal (.app (.app (.const `Iff []) other) foundPattern)
          ((CExpr.const `Eq.ndrec [v,1]).mkApp [(.sort 0),other,motiveT,.bvar 1,foundPattern,((CExpr.const `propext []).mkApp [other,foundPattern,(.bvar 0)])])
         .default
        )
      .default
    | _ => .failed

/-
We should add a new BackType and a new context where we record this ↑ construction.
We then add it as a Backstep, with two arguements. The children should be the new
goal (aka. `motive a`) and another backstep, which should be the rw-thorem as a normal
backstep, with its subgoals.
At assembly, for the backstep with this Backtype, we use this `mkRWBackThing` as head.
-/

--#exit

partial def findPattern (p ce : CExpr) : List (List oDirs) :=
  let rec go (done : List (List oDirs)) :
    List (CExpr × List oDirs) → List (List oDirs)
    | [] => done
    | (here,ds) :: xs =>
        if here == p --hopefully not up to original data for gnode lnodes
        then go (ds :: done) xs
        else
          match ce with
          | .app f a => go done ((f,.apf :: ds) :: (a,.apa :: ds) :: xs)
          | .lam _ f a _ => go done ((f,.laf :: ds) :: (a,.laa :: ds) :: xs)
          | .forallE _ f a _ => go done ((f,.alf :: ds) :: (a,.ala :: ds) :: xs)
          | .letE _ f a z _ => go done ((f,.lef :: ds) :: (a,.lea :: ds) :: (z,.lez :: ds) :: xs)
          | .proj _ _ e => go done ((e,.pro :: ds) :: xs)
          | _ => go done xs
   go [] [(ce,[])]


def mkRWForwThing (fctx : FixCtx) (dirs : List oDirs) (foundPattern other within : CExpr) : CExpr :=
  let Ptype := CExpr.whnf fctx (CExpr.inferType fctx foundPattern) -- buggggsssss from fctx
  let PtypeT := CExpr.whnf fctx (CExpr.inferType fctx Ptype)
  match PtypeT with
  | .sort u =>
    let motive := factorOnDirs dirs within Ptype
    let motiveT := CExpr.whnf fctx (CExpr.inferType fctx motive)
    match PtypeT with
    | .forallE _ _ (.sort v) _ =>
      .lam `nextgoal (replaceAt dirs within other)
        (.lam `eqgoal (.app (.app (.app (.const `Eq [u]) Ptype) foundPattern) other)
          ((CExpr.const `Eq.ndrec [v,u]).mkApp [Ptype,foundPattern,motiveT,.bvar 1,other,.bvar 0])
         .default
        )
      .default
    | _ => .failed
  | _ => .failed


#check_failure EmbedStruct.embed -- import pain

/-
- embed eq thm, add it to ltx and assembly
- look for patterns in ltx via `findPattern`
- if there is, make new gnode with type derived via `replaceAt`
- to build it, in `ltx_assembly` add entry with the new kind of backtype
  with two arguments : first, the gnode that the pattern was found in,
  second, the the gnode corresponding to the embedded thm
-/


/-
Todo:
- Local rws, ie. those from equalities that are hyps, or where introduced as previous
  gnodes.
- Long term idea: maintain CExprTrie of patterns, and have following trigger ;
  at each newly introduced expression, check if it or one of its subterms is one of
  the patterns, and carry out the rewrites
-/
