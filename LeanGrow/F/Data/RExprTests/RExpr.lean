
import Lean


open Lean

#check 1

instance : BEq InductiveVal where
  beq := fun a b =>
    a.toConstantVal == b.toConstantVal &&
    a.numParams == b.numParams &&
    a.numIndices == b.numIndices &&
    a.all == b.all &&
    a.ctors == b.ctors &&
    a.isRec == b.isRec &&
    a.isNested == b.isNested &&
    a.isUnsafe == b.isUnsafe &&
    a.isReflexive == b.isReflexive


instance : BEq QuotKind where
  beq := fun a b =>
    match a, b with
    | .type, .type => true
    | .ctor, .ctor => true
    | .lift, .lift => true
    | .ind, .ind => true
    | _, _ => false

instance : BEq QuotVal where
  beq := fun a b =>
    a.toConstantVal == b.toConstantVal &&
    a.kind == b.kind



inductive RExpr where
| lnode : Nat → Option Nat → RExpr
| gnode : Nat → RExpr
| bvar : Nat → RExpr
| sort : Level → RExpr
| axm : Name → List Level → RExpr
| ctor : ConstructorVal → List Level → RExpr
| indt : InductiveVal → List Level → RExpr
-- ↑ may be smart to do in preprocess, so that we don't have to check if inductive type when seeking to apply induction
| quo : QuotVal → List Level → RExpr
| deltaDef : Name → List Level → RExpr
-- ↑ ↓ for delta refer to `Lean.ReducibilityHints` and `Lean.Meta.isDefEqDeltaStep` in `Lean > Meta > ExprDefEq`
| deltaFun : Name → List Level → RExpr -- for function definitions, so as to be used for nable (makes the nabla constructor useless)
-- We should also keep a context where lnodes & gnodes that are funcitons are collected, so that we try nabla in these cases too
| app : RExpr → RExpr → RExpr
| lam : Name → RExpr → RExpr → BinderInfo → RExpr -- make sure nabla applies here too.. or not, as it also creates betas... possible loop ?
| forallE : Name → RExpr → RExpr → BinderInfo → RExpr
| lit : Literal → RExpr
| proj : Name → Nat → RExpr → RExpr
| struc : Name → List RExpr → RExpr -- for constants of a structure type ?!? projections as list
-- to be determined according to `Lean.isStructureLike`
-- OptParam and OutParam ... are gonna be painful
| failed : RExpr
--| beta : Name → RExpr → RExpr → BinderInfo → RExpr → RExpr -- probably best to keep a local context at unification to see which bvars to replace by what
| recu : Name → List Level → List RExpr → RExpr
| mat : Name → List Level → List RExpr → RExpr
-- we will need an enironment for ↑
| rw : Nat → RExpr
-- ↑ should only be introduced at search-time, and links to the id of the rw-class
| proof : RExpr → RExpr → RExpr
-- ↑ by proof irrelevance, we only have to chek that the propositions unify, to get that the types are equal ...
-- as seems to be noted in `isDefEqEtaStruct`, proof irrelevance can cause less eager unification
-- (if the proofs are the same up to mvars, this would have been the chance to assigne mvars ???)
deriving Inhabited, BEq--, Repr

#check ConstantInfo


inductive NodeExpr where
| ofLNode (i : Nat) (tag : Option Nat)
| ofGNode (i : Nat)
| ofRExpr (c : RExpr)
deriving Inhabited, BEq

inductive IotaWrap where
| ofRec (r : List (((Array RExpr) × RExpr) × RExpr))
/- ↑ is the equivalent of a list of `RecursorRule`.
Instead of the ctor name, we hav it in embedable form,
where the array corresponds to the params and the second
elem in the pair corresponds to the head.
The last RExpr is the rhs, which we should replace the `.rec`
with in case of a match, so that the rediction can then be performed
with more betas. Indeed, we expect the args to `RExpr.recu` to be the
motive and the replacement rules
-/
| ofMatch (q : List ((Array RExpr) × (List RExpr) × RExpr))
/- ↑ list of alternatives corresponding to `eq_`, where the first
element in the triple refers to the types of the lnodes in the arguments
that are being matched on (secomd in triple) and the righ-hand-side
(third in triple).
-/


/-
**Notes**

- for deltaDef and deltaFun, we should, at cache build time, get rid of abbreviations by checking that
  the constant doesn't unfld to a constant (else, keep unfolding until this is false, and use that as val)

- We should eta expand all structures before caching. This needs to be done in every expression.
  For example in `.lam _ T B _`, if `T` is a structure, we should replace, in `B`, all occurences
  of `.bvar x` with `T.mk (.proj T 0 (.bvar x)) (.proj T 1 (.bvar x)) ...`.

-/
