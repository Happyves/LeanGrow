
import Lean


open Lean

#check 1

inductive RExpr where
| lnode : Nat → Option Nat → RExpr
| gnode : Nat → RExpr
| bvar : Nat → RExpr
| sort : Level → RExpr
| axm : Name → List Level → RExpr
| ctor : Name → List Level → RExpr -- to change, likely
| indt : Name → List Level → RExpr
-- ↑ may be smart to do in preprocess, so that we don't have to check if inductive type when seeking to apply induction
| quo : Name → List Level → RExpr
| deltaDef : Name → List Level → RExpr
-- ↑ ↓ for delta refer to `Lean.ReducibilityHints` and `Lean.Meta.isDefEqDeltaStep` in `Lean > Meta > ExprDefEq`
| deltaFun : Name → List Level → RExpr -- for function definitions, so as to be used for nable (makes the nabla constructor useless)
-- We should also keep a context where lnodes & gnodes that are funcitons are collected, so that we try nabla in these cases too
| deltaThm : Name → List Level → RExpr -- Lean stores defs with Prop types as defs → when making RExpr, check if type is Prop !!
| app : RExpr → RExpr → RExpr
| lam : Name → RExpr → RExpr → BinderInfo → RExpr -- make sure nabla applies here too.. or not, as it also creates betas... possible loop ?
| forallE : Name → RExpr → RExpr → BinderInfo → RExpr
| letE : Name → RExpr → RExpr → RExpr → Bool → RExpr -- should be treated as ζ node and act like beta ↓
| lit : Literal → RExpr
| proj : Name → Nat → RExpr → RExpr
| struc : List RExpr → RExpr -- for constants of a structure type ?!? projections as list
-- OptParam and OutParam ... are gonna be painful
| failed : RExpr
| hole : RExpr
| beta : Name → RExpr → RExpr → BinderInfo → RExpr → RExpr -- probably best to keep a local context at unification to see which bvars to replace by what
| nabla : RExpr → RExpr --should be wraped around constants (technically also lambdas ?!?) that have a function type
| pRec : RecursorVal → RExpr
--| iota : RecursorVal → (motive : RExpr) → (branches : List RExpr) → (arg : RExpr) →  RExpr
-- ↑ It might actually be best to systematically reduce ι, as this requires less comparisons durring
-- unification, without leading to a term size explosion, as may happen in β or ζ
| rw : Nat → RExpr
-- ↑ should only be introduced at search-time, and links to the id of the rw-class
| proof : RExpr → RExpr
-- ↑ by proof irrelevance, we only have to chek that the propositions unify, to get that the types are equal ...
-- as seems to be noted in `isDefEqEtaStruct`, proof irrelevance can cause less eager unification
-- (if the proofs are the same up to mvars, this would have been the chance to assigne mvars ???)

--deriving Inhabited, BEq, Repr

#check ConstantInfo
