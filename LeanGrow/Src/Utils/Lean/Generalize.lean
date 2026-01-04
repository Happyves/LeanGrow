
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Lean.Meta.Tactic.Util
import LeanGrow.Src.Utils.LeanGrow.Expr


open Lean Meta

/-
- add workers to tests
- remove patc fvars from local inst in a cleaning function to be runonce every grow-iteration
- \d should use Prod5 and return ltxs
-/






@[specialize]
partial def generalizeProofsIgnoringMain
  (initD : LocalContext) (initI : LocalInstances)
  (type: Expr) (extWorkers : Array FVarId) (ignore prohibProof : Expr → LocalContext → LocalInstances → MetaM Bool)
  : MetaM (Prod4 Expr ((Array Expr) × (Array Expr)) LocalContext LocalInstances) := do
  mtracing
  Lean.Expr.onAllSubtermsWiWorkerCpsSkipTravState type initD initI ((#[], #[] ): Array Expr × Array Expr)
    (fun e depth F@(factors, factypes) initD initI => do
      mtrace on .zero with s!"[generalizeProofsIgnoringMain] looking at {← ppExpr e}"
      if ← (IsProof e initD initI <&&> prohibProof e initD initI)
      then
        let (absd, absdWs) ← e.abstractInnerWorkers extWorkers initD initI
        mtrace on .zero with s!"[generalizeProofsIgnoringMain] worker fvars in proof: {repr absdWs}"
        mtrace on .zero with s!"[generalizeProofsIgnoringMain] abstracted proof to {← ppExpr absd}"
        let absdT ← InferType absd initD initI
        mtrace on .zero with s!"[generalizeProofsIgnoringMain] with type {← ppExpr absdT}"
        let .mk genT (genFac, genFacT) initD initI ← generalizeProofsIgnoringMain initD initI absdT extWorkers ignore prohibProof -- for the case that the proof's type contains further proofs !
        let factors := factors ++ genFac
        let factypes := factypes ++ genFacT
        let args ← absdWs.filterM (fun x => do match ← x.fvarId!.GetDecl initD initI with | .cdecl .. => return true | _ => return false)
          -- absd is lambda let bound, and we want it to only be in an application with the lambda args
        let rep := mkAppN (.bvar (depth + factors.size)) args
        let factors := factors.push absd
        let factypes := factypes.push genT -- genT isn't the actual type of absd ; it is when instantiated with genFac
        mtrace on .zero with s!"[generalizeProofsIgnoringMain] replacing by {rep}"
        mtrace on .two with s!"[generalizeProofsIgnoringMain] (factors, factypes) : {← factors.mapM ppExpr} {← factypes.mapM ppExpr}"
        return ⟨(.error rep), (factors, factypes),initD,initI⟩ -- instruct `onAllSubtermsWiWorkerCpsSkipTravState` to skip, for convenience
      else
        if ← ignore e initD initI
        then
          mtrace on .zero with s!"[generalizeProofsIgnoringMain] subexpression was ignored"
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
  let .mk res (factors, factypes) l1 l2 ← generalizeProofsIgnoringMain initD initI type extWorkers ignore prohibProof
  mtrace on .one with s!"[generalizeProofsIgnoring] main returned :\n{res}\n{← factors.mapM ppExpr}\n{← factypes.mapM ppExpr}"
  let mut res := res
  for T in factypes do
    res := .forallE `generalize T res .default
  return ⟨res, factors.reverse,l1,l2⟩


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
      let tns := p.getTnodes
      withLCtx l1 l2 <| tns.anyM (fun tn => do
        let r ← isProof tn
        return !r
        )
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
