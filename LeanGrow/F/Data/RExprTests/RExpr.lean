
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
| deltaFun : Name → List Level → RExpr -- for function definitions, so as to be used for nable (makes the nabla constructor useless)
| deltaThm : Name → List Level → RExpr
| app : RExpr → RExpr → RExpr
| lam : Name → RExpr → RExpr → BinderInfo → RExpr -- make sure nabla applies here too.. or not, as it also creates betas... possible loop ?
| forallE : Name → RExpr → RExpr → BinderInfo → RExpr
| letE : Name → RExpr → RExpr → RExpr → Bool → RExpr -- should be treated as ζ node and act like beta ↓
| lit : Literal → RExpr
| proj : Name → Nat → RExpr → RExpr
| struc : List RExpr → RExpr -- for constants of a structure type ?!? projections as list
| failed : RExpr
| beta : Name → RExpr → RExpr → BinderInfo → RExpr → RExpr -- probably best to keep a local context at unification to see which bvars to replace by what
| nabla : RExpr → RExpr --should be wraped around constants (technically also lambdas ?!?) that have a function type
| pRec : RecursorVal → RExpr
--| iota : RecursorVal → (motive : RExpr) → (branches : List RExpr) → (arg : RExpr) →  RExpr
-- ↑ It might actually be best to systematically reduce ι, as this requires less comparisons durring
-- unification, without leading to a term size explosion, as may happen in β or ζ
| rw : Nat → RExpr
-- ↑ should only be introduced at search-time, and links to the id of the rw-class
--deriving Inhabited, BEq, Repr

#check ConstantInfo
