
import LeanGrow.F.Data.RExprTests.API
import LeanGrow.F.Data.CExpr.Types
import Lean.Structure

open Lean

#check isStructure
#check getStructureCtor


def myMkProjFuns
  (structName : Name) (structLevel : List Level) (structParams : List RExpr)
  (numFields : Nat) (toExpand : RExpr) : RExpr :=
  let projs := (List.range numFields).map (fun i => RExpr.proj structName i toExpand)
  .struc structName structLevel structParams projs

structure StrucData where
  name : Name
  lvls : List Level
  params : List RExpr
  numFields : Nat


def RExpr.isStructureNaive (env : Environment) (re : RExpr) : Option StrucData :=
  let (h, as) := RExpr.getApp re
  match h with
  | .indt strucName ({ isRec := false, ctors := [ctorName], .. }) lvls =>
    -- not proposition valued ones, following `Lean.Meta.toCtorWhenStructure` in Lean > Meta > WHNF
        match env.find? ctorName with
        | .some (.ctorInfo I) =>
              let nf := I.numParams
              -- following `Lean.Meta.toCtorWhenStructure` in Lean > Meta > WHNF
              .some ⟨strucName, lvls, as, nf⟩
        | _ => .none
  | _ => .none





#exit

/--
When building CExpr, we must now consider the lnodes/gnodes that have structure types,
so that we may eta expand them in future types.

Note, this function doesn't reduce the binding types (yet), so bvars bound by types
that aren't-but-reduce-to structures will not be expanded.
-/
def RExpr.etaBinders (env : Environment) (etaLGnodes : List Nat) (etaBvars : List Nat) : RExpr → RExpr
| .failed m => .failed m
| .lnode i t => .lnode i t
| .gnode i => .gnode i
| .bvar i =>
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
| letE : Name → RExpr → RExpr → RExpr → Bool → RExpr
| lit : Literal → RExpr
| proj : Name → Nat → RExpr → RExpr
| struc : Name → List RExpr → RExpr -- for constants of a structure type ?!? projections as list
-- to be determined according to `Lean.isStructureLike`
-- OptParam and OutParam ... are gonna be painful
| failed : String → RExpr
--| beta : Name → RExpr → RExpr → BinderInfo → RExpr → RExpr -- probably best to keep a local context at unification to see which bvars to replace by what
| recu : Name → List Level → List RExpr → RExpr
| mat : Name → List Level → List RExpr → RExpr
-- we will need an enironment for ↑
| rw : Nat → RExpr
-- ↑ should only be introduced at
