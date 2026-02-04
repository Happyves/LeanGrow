
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Lean.Meta.Tactic.Util
import LeanGrow.Src.Utils.LeanGrow.Expr


open Lean Meta



@[specialize,inline]
partial def Lean.Expr.onAllSubtermsWiWorkerCpsSkipTravExpectingState (e : Expr) (l1 : LocalContext) (l2 : LocalInstances) {β: Sort _} (init : β)
  (f : Expr → Expr → Nat → β → LocalContext → LocalInstances → MetaM (Prod4 (Except Expr Expr) β LocalContext LocalInstances))
  : MetaM (Prod4 Expr β LocalContext LocalInstances) :=
   let rec @[specialize f] go (state : β) (e ET : Expr) (d : Nat) (l1 : LocalContext) (l2 : LocalInstances)
    : MetaM (Prod4 Expr β LocalContext LocalInstances) := do
      let ⟨R,state,l1,l2⟩ ← f e ET d state l1 l2
      match R with
      | .ok R =>
          match R with
          | .app l r =>
            let (etl,etr) ← (do
              let lt ← InferType l l1 l2
              match lt with
              | .forallE _ T _ _ => return (lt,T)
              | _ =>
                let lt' ← Whnf lt l1 l2
                match lt' with
                | .forallE _ T _ _ => return (lt,T)
                | _ => panic! s!"[onAllSubtermsWiWorkerCpsSkipTravExpectingState] not fn type ?"
                )
            let ⟨l,state,l1,l2⟩ ← go state l etl d l1 l2
            let ⟨r,state,l1,l2⟩ ← go state r etr d l1 l2
            let R := .app l r
            return ⟨R,state,l1,l2⟩
          | .lam n l r bi =>
            let etr ← (do
              match ET with
              | .forallE _ _ V _ => return V
              | _ =>
                let lt ← Whnf ET l1 l2
                match lt with
                | .forallE _ _ V _ => return V
                | _ => panic! s!"[onAllSubtermsWiWorkerCpsSkipTravExpectingState] not fn type ?"
                )
            let ⟨l,state,l1,l2⟩ ← go state l (← InferType l l1 l2) d l1 l2
            let S := l2.size
            let fv ←  worker d
            let ⟨fv,r,l1,l2⟩ ← withFreeing fv l r l1 l2
            let ⟨r,state,l1,l2⟩ ← go state r etr (d+1) l1 l2
            let l2 := match bi with | .instImplicit => l2.patch S 1 | _ => l2
            let r := r.abstract #[.fvar fv]
            let R := .lam n l r bi
            return ⟨R,state,l1,l2⟩
          | .forallE n l r bi =>
            let ⟨l,state,l1,l2⟩ ← go state l (← InferType l l1 l2) d l1 l2
            let S := l2.size
            let fv ←  worker d
            let ⟨fv,r,l1,l2⟩ ← withFreeing fv l r l1 l2
            let ⟨r,state,l1,l2⟩ ← go state r (← InferType r l1 l2) (d+1) l1 l2
            let l2 := match bi with | .instImplicit => l2.patch S 1 | _ => l2
            let r := r.abstract #[.fvar fv]
            let R := .forallE n l r bi
            return ⟨R,state,l1,l2⟩
          | .letE n L r z bi =>
            let ⟨l,state,l1,l2⟩ ← go state L (← InferType L l1 l2) d l1 l2
            let ⟨r,state,l1,l2⟩ ← go state r L d l1 l2
            let S := l2.size
            let fv ←  worker d
            let ⟨fv,z,l1,l2⟩ ← withFreeingLet fv l r z l1 l2
            let ⟨z,state,l1,l2⟩ ← go state z (← InferType z l1 l2) (d+1) l1 l2
            let l2 := if (← withLCtx l1 l2 (isClass? l)).isSome then l2.patch S 1 else l2
            let z := z.abstract #[.fvar fv]
            let R := .letE n l r z bi
            return ⟨R,state,l1,l2⟩
          | .proj n i L =>
            let ⟨l,state,l1,l2⟩ ← go state L (← InferType L l1 l2) d l1 l2
            let R := .proj n i l
            return ⟨R,state,l1,l2⟩
          | .mdata da l =>
            let ⟨l,state,l1,l2⟩ ← go state l ET d l1 l2
            let R := .mdata da l
            return ⟨R,state,l1,l2⟩
          | t => return ⟨t,state,l1,l2⟩
      | .error R =>
          return ⟨R,state,l1,l2⟩
  do
  go init e (← InferType e l1 l2) 0 l1 l2



@[specialize]
partial def generalizeProofsIgnoringMain
  (initD : LocalContext) (initI : LocalInstances)
  (type: Expr) (extWorkers : Array FVarId) (ignore prohibProof : Expr → LocalContext → LocalInstances → MetaM Bool)
  : MetaM (Prod4 Expr (Prod3 (Array Expr) (Array Expr) (Array Expr)) LocalContext LocalInstances) := do
  mtracing
  Lean.Expr.onAllSubtermsWiWorkerCpsSkipTravExpectingState type initD initI ((.mk #[] #[] #[]) : Prod3 (Array Expr) (Array Expr) (Array Expr))
    (fun e ET _ F@(.mk factors factypes facFvs) initD initI => do
      mtrace on .one with s!" looking at {← ppExpr e}\nET {← ppExpr ET}"
      if ← (IsProof e initD initI <&&> prohibProof e initD initI)
      then
        mtrace on .zero with s!" found proof {← ppExpr e}"
        let .mk absd forDbg initD initI ← e.abstractInnerWorkers extWorkers initD initI
        mtrace on .zero with s!" worker fvars in proof: {repr forDbg}"
        mtrace on .zero with s!" abstracted proof to {← ppExpr absd}"
        -- let absdT ← InferType absd initD initI
        let .mk absdT absdWs initD initI ← ET.abstractInnerWorkersAll extWorkers initD initI
        mtrace on .zero with s!" worker fvars in expected type: {repr absdWs}"
        mtrace on .zero with s!" abstracted expected type to {← ppExpr absdT}"
        let .mk genT (.mk genFac genFacT genFvs) initD initI ← generalizeProofsIgnoringMain initD initI absdT extWorkers ignore prohibProof -- for the case that the proof's type contains further proofs !
        let factors := factors ++ genFac
        let factors := factors.push absd
        let factypes := factypes ++ genFacT
        let factypes := factypes.push genT -- genT isn't the actual type of absd ; it is when instantiated with genFac
        let facFvs := facFvs ++ genFvs
        let dummy := Expr.fvar ⟨← mkFreshId⟩
        let facFvs := facFvs.push dummy
        let args ← absdWs.filterM (fun x => do match ← x.GetDecl initD initI with | .cdecl .. => return true | _ => return false)
          -- absd is lambda let bound, and we want it to only be in an application with the lambda args
        let rep := mkAppN dummy (args.map Expr.fvar)
        mtrace on .zero with s!" replacing by {rep}"
        mtrace on .two with s!" (factors, factypes) : {← factors.mapM ppExpr} {← factypes.mapM ppExpr}"
        return ⟨(.error rep), (.mk factors factypes facFvs),initD,initI⟩ -- instruct `onAllSubtermsWiWorkerCpsSkipTravState` to skip, for convenience
      else
        if ← ignore e initD initI
        then
          mtrace on .zero with s!" subexpression was ignored"
          return ⟨(.error e),F,initD,initI⟩
        else
          return ⟨(.ok e),F,initD,initI⟩
      )



/-- Given `type`, (recursively) find proof inside it and bastract them.
The continuation expects the ∀-bounded version of the abstracted `type`,
with props of abstracted proofs (or predicates, if withing binders) as binders.
Note that predicates can contain let-bindings.
The array passed to the continuation corresponds to the proofs(/predicates) of the
original `type`.

`ignore` corresponds to a pattern to skip, as will be needed for rewriting.
*Note* : we could eaily adapt `ignore` to be in cps.

`prohibProof` decides if the proof should be abstracted. In the context of rewriting
for example, it may not need to, if it doesn't depend on the pattern (in the unsafe
sense that it doesn't contain the pattern in its prop).

Note that in the backward context, we may end up generalizing proofs that contain,
or who's type contains, tnodes.
-/
@[inline, specialize]
def generalizeProofsIgnoring
  (initD : LocalContext) (initI : LocalInstances)
  (type : Expr) (extWorkers : Array FVarId) (ignore prohibProof : Expr → LocalContext → LocalInstances → MetaM Bool)
  : MetaM (Prod4 Expr (Array Expr) LocalContext LocalInstances) := do
  mtracing
  let .mk res (.mk factors factypes facFvs) l1 l2 ← generalizeProofsIgnoringMain initD initI type extWorkers ignore prohibProof
  mtrace on .one with s!"[generalizeProofsIgnoring] main returned :\n{res}\n{← factors.mapM ppExpr}\n{← factypes.mapM ppExpr}"
  let mut res := res
  let mut i := factypes.size - 1
  for _ in List.range factypes.size do
    let T := factypes[i]!
    let fv := facFvs[i]!
    res := .forallE `generalize T (res.abstract #[fv]) .default
    i := i-1
  return ⟨res, factors,l1,l2⟩




/-- Given `type`, (recursively) find proof inside it and bastract them.
The continuation expects the ∀-bounded version of the abstracted `type`,
with props of abstracted proofs (or predicates, if withing binders) as binders.
Note that predicates can contain let-bindings.
The array passed to the continuation corresponds to the proofs(/predicates) of the
original `type`
-/
def generalizeProofs
  (initD : LocalContext) (initI : LocalInstances)
  (type : Expr) (extWorkers : Array FVarId)
  : MetaM (Prod4 Expr (Array Expr) LocalContext LocalInstances) := do
  generalizeProofsIgnoring initD initI type extWorkers (fun _ _ _ => return false) (fun _ _ _ => return true)




@[inline, specialize]
def generalizeTnodesSafeIgnoring
  (initD : LocalContext) (initI : LocalInstances)
  (type : Expr) (extWorkers : Array FVarId) (ignore : Expr → LocalContext → LocalInstances → MetaM Bool)
  : MetaM (Prod4 (Option Expr) (Array Expr) LocalContext LocalInstances) := do
  mtracing
  let .mk res factors l1 l2 ← generalizeProofsIgnoring initD initI type extWorkers ignore
    (fun p l1 l2 => do
      let w? :=
        match p.fvarId? with
        | .some i => i.isWorker
        | _ => false
      if w?
      then return false
      else
        let tns := p.getTnodes
        withLCtx l1 l2 <| tns.allM isProof
      )
  if res.hasTnodes
  then return .mk .none #[] l1 l2
  else return .mk (.some res) factors l1 l2



#exit

@[specialize]
partial def generalizeTnodesSafeIgnoringMain
  (initD : LocalContext) (initI : LocalInstances)
  (fst? : Bool) (type : Expr) (extWorkers : Array FVarId) (ignore prohibTnodeFst prohibTnodeHard : Expr → LocalContext → LocalInstances → MetaM Bool)
  : MetaM (Prod4 Expr (Option (Array Expr × Array Expr)) LocalContext LocalInstances) := do
  mtracing
  Lean.Expr.onAllSubtermsWiWorkerCpsSkipTravState type initD initI ((#[], #[] ): Array Expr × Array Expr)
    (fun e depth F initD initI  => do
      match F with
      | .none =>
          return ⟨(.error e), F, initD, initI⟩
      | .some (factors, factypes) =>
          match e with
          | .fvar ⟨(.num (.num _ _) _)⟩ =>
              mtrace on .zero with s!"[generalizeTnodesSafeIgnoringMain] found tnode {← ppExpr e}"
              if ← (if fst? then (prohibTnodeFst e initD initI) else (prohibTnodeHard e initD initI))
              then
                mtrace on .zero with s!"[generalizeTnodesSafeIgnoringMain] prohibition predicates were ture (fst? {fst?})"
                let eT ← InferType e initD initI
                mtrace on .zero with s!"[generalizeTnodesSafeIgnoringMain] tnode of type {← ppExpr eT}"
                let (eT, absdWs) ← e.abstractInnerWorkersAll extWorkers initD initI
                mtrace on .zero with s!"[generalizeTnodesSafeIgnoringMain] abstracted workers to {← ppExpr eT}"
                if ← IsProp eT initD initI
                then
                  let .mk genT ok? initD initI ← generalizeTnodesSafeIgnoringMain initD initI false eT extWorkers ignore prohibTnodeFst prohibTnodeHard
                  match ok? with
                  | .none => return ⟨(.error e), ok?, initD, initI⟩
                  | .some (genFac, genFacT) =>
                    let factors := factors ++ genFac
                    let factypes := factypes ++ genFacT
                    let args ← absdWs.filterM (fun x => do match ← x.fvarId!.GetDecl initD initI with | .cdecl .. => return true | _ => return false)
                      -- absd is lambda let bound, and we want it to only be in an application with the lambda args
                    let rep := mkAppN (.bvar (depth + factors.size)) args
                    let factors := factors.push e
                    let factypes := factypes.push genT -- genT isn't the actual type of eT ; it is when instantiated with genFac
                    mtrace on .zero with s!"[generalizeTnodesSafeIgnoringMain] returned from types of {← ppExpr e}, replacing it by {rep}"
                    mtrace on .one with s!"[generalizeTnodesSafeIgnoringMain] current factors\n{← factors.mapM ppExpr}\ncurrent factype\n{← factypes.mapM ppExpr}"
                    return ⟨(.error rep), (factors, factypes), initD, initI⟩
                else
                  return ⟨(.error e), .none, initD, initI⟩
              else
                if ← ignore e initD initI
                then
                  mtrace on .zero with s!"[generalizeTnodesSafeIgnoringMain] tnode was ignored"
                  return ⟨(.error e), F, initD, initI⟩
                else
                  return ⟨(.ok e), F, initD, initI⟩
          | _ =>
              if ← ignore e initD initI
              then
                mtrace on .zero with s!"[generalizeTnodesSafeIgnoringMain] term {← ppExpr e} was ignored"
                return ⟨(.error e), F, initD, initI⟩
              else
                return ⟨(.ok e), F, initD, initI⟩
      )


/--

We need this in the context of tnodes instead of `generalizeProofsIgnoring`, since for example,
for some predicate `P : Nat → Prop` and some Nat-typed tnode t, `P t` is a proof that whould
get abstracted, but we don't want it to, as we loose information for unification ...
-/
@[inline, specialize]
def generalizeTnodesSafeIgnoring
  (initD : LocalContext) (initI : LocalInstances)
  (type : Expr) (extWorkers : Array FVarId) (ignore prohibTnodeFst prohibTnodeHard : Expr → LocalContext → LocalInstances → MetaM Bool)
  : MetaM (OptionProd4 Expr (Array Expr) LocalContext LocalInstances) := do
  mtracing
  let .mk res ok? l1 l2 ← generalizeTnodesSafeIgnoringMain initD initI true type extWorkers ignore prohibTnodeFst prohibTnodeHard
  mtrace on .zero with s!"[generalizeTnodesSafeIgnoring] main returned: {← ppExpr res}"
  match ok? with
  | .none => return .none
  | .some (factors, factypes) =>
      let mut res := res
      for T in factypes do
        res := .forallE `generalize T res .default
      mtrace on .zero with s!"[generalizeTnodesSafeIgnoring] after attaching ∀s: {← ppExpr res}"
      return .some res factors.reverse l1 l2
