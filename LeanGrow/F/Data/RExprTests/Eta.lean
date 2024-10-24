
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
  | .indt strucName ({ toConstantVal := CV, isRec := false, ctors := [ctorName], .. }) lvls =>
    -- not proposition valued ones, following `Lean.Meta.toCtorWhenStructure` in Lean > Meta > WHNF
      match (Expr.getAppFn CV.type) with
      | .sort .zero => .none -- not up to reductions, though :(
      | _ =>
          match env.find? ctorName with
          | .some (.ctorInfo I) =>
                let nf := I.numParams
                -- following `Lean.Meta.toCtorWhenStructure` in Lean > Meta > WHNF
                .some ⟨strucName, lvls, as, nf⟩
          | _ => .none
  | _ => .none

def RExpr.isStrucCtorNaive (env : Environment) (re : RExpr) : Bool :=
  let (h, _) := RExpr.getApp re
  match h with
  | .ctor _ ({toConstantVal := CV, ..}) _ =>
      let h := Expr.getAppFn (Expr.getForallBody CV.type)
      match h with
      | .const n _ => Lean.isStructure env n
      | _ => false
  | _ => false



/--
When building CExpr, we must now consider the lnodes/gnodes that have structure types,
so that we may eta expand them in future types.

Note, this function doesn't reduce the binding types (yet), so bvars bound by types
that aren't-but-reduce-to structures will not be expanded.
-/
partial def RExpr.etaBinders (env : Environment)
  (etaLnodes : List (Nat × StrucData)) (etaGnodes : List (Nat × StrucData))
  (on : RExpr) : RExpr :=
  let rec go (etaBvars : List (StrucData)) : RExpr → RExpr
    | .lnode i t =>
          match etaLnodes.find? (fun x => x.1 == i) with
          | .none => .lnode i t
          | .some (_, data) => myMkProjFuns data.name data.lvls data.params data.numFields (.lnode i t)
    | .gnode i =>
          match etaGnodes.find? (fun x => x.1 == i) with
          | .none => .gnode i
          | .some (_, data) => myMkProjFuns data.name data.lvls data.params data.numFields (.gnode i)
    | .bvar i =>
          match etaBvars.get? i with
          | .none => .bvar i
          | .some data => myMkProjFuns data.name data.lvls data.params data.numFields (.bvar i)
    | .lam n t b i =>
        match RExpr.isStructureNaive env t with
        | .none =>
              let T := go etaBvars t
              let B := go etaBvars b
              .lam n T B i
        | .some SD =>
              let T := go etaBvars t
              let B := go (SD :: etaBvars) b
              .lam n T B i
    | .forallE n t b i =>
        match RExpr.isStructureNaive env t with
        | .none =>
              let T := go etaBvars t
              let B := go etaBvars b
              .forallE n T B i
        | .some SD =>
              let T := go etaBvars t
              let B := go (SD :: etaBvars) b
              .forallE n T B i
    | .letE n t v b i =>
          match RExpr.isStructureNaive env t with
        | .none =>
              let T := go etaBvars t
              let V := go etaBvars v
              let B := go etaBvars b
              .letE n T V B i
        | .some data =>
              if RExpr.isStrucCtorNaive env v
              then
                let T := go etaBvars t
                let V := go etaBvars v
                let B := go etaBvars b
                .letE n T V B i
              else
                let T := go etaBvars t
                let V := go etaBvars v
                let fV := myMkProjFuns data.name data.lvls data.params data.numFields V
                let B := go etaBvars b
                .letE n T fV B i
    | .proj n i e => .proj n i (go etaBvars e)
    | .app l r => .app (go etaBvars l) (go etaBvars r)
    | .proof l r => .proof (go etaBvars l) (go etaBvars r)
    | .struc n lvl ps as =>
          let F := go etaBvars
          .struc n lvl (ps.map F) (as.map F)
    | .recu n lvl as =>
          let F := go etaBvars
          .recu n lvl (as.map F)
    | .mat n lvl as =>
          let F := go etaBvars
          .mat n lvl (as.map F)
    | x => x
  go [] on
