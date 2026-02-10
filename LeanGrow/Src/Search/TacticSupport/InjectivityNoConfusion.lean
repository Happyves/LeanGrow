
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrowAlpha.Final.Search.API.IntegrateForw
import LeanGrowAlpha.Final.Search.API.IntegrateBack

open Lean Meta


/-- Continuation is like for integrateBackwardStd and forw case :
exacts etheir the newly added forw id of the applicaiton of the inj-thm,
or the list of propaed goals from the backstep that is noConfusion-/
def injectivityOrNoConfusionOrLeave
  (target_forw_id : Nat) (target_forw_type : Expr) (goalI : Nat) (goalE : Expr)
  (revCountMax : Nat) (st : SearchState (List Nat))
  {α : Sort _} (k : Bool → ListProd Nat Expr → ListProd Nat Expr → SearchState (List Nat) → MetaM α) : MetaM α :=
  trace set Tracing.Flags.none in do
  mtrace on .zero with s!"[injectivityOrNoConfusionOrLeave] call on {← ppExpr target_forw_type}"
  match target_forw_type.eq? with
  | .none => k false .nil .nil st
  | .some (T,l,r) =>
      if ← isProp T
      then
        mtrace on .zero with s!"[injectivityOrNoConfusionOrLeave] equality of props, skipping"
        k false .nil .nil st
      -- though `And.noConfusion` is a thing ... in most cases noConfusion and inj don't exist
      else
      let T ← whnfD T -- as in `Lean.Meta.mkNoConfusion`
      matchConstInduct T.getAppFn (fun _ => k false .nil .nil st) fun v us => do
        -- ↓ also lifts literals
        let .some L ← isConstructorApp? (← whnfD l) | k false .nil .nil st
        let .some R ← isConstructorApp? (← whnfD r) | k false .nil .nil st
        mtrace on .zero with s!"[injectivityOrNoConfusionOrLeave] eq of constructors"
        if L.cidx == R.cidx
        then
          mtrace on .zero with s!"[injectivityOrNoConfusionOrLeave] same index"
          let injN := mkInjectiveTheoremNameFor L.name
          if (← getEnv).contains injN
          then
            mtrace on .zero with s!"[injectivityOrNoConfusionOrLeave] equality of props, skipping"
            let ugn := if st.uNodes.binSearchContains target_forw_id (· < ·) then unode target_forw_id else gnode target_forw_id
            try
              let term ← mkAppM injN #[.fvar ⟨ugn⟩]
              if !(← isTypeCorrect term)
              then
                mtrace on .zero with s!"[injectivityOrNoConfusionOrLeave] term not type correct ?!"
                k false .nil .nil st
              else
                mtrace on .zero with s!"[injectivityOrNoConfusionOrLeave] success, integrating term {← ppExpr term} with ugInds {target_forw_id}"
                integrateForwardStd
                  revCountMax (.other) term [target_forw_id] st
                  <| fun new exp st => k true (.cons new exp .nil) .nil st
            catch _ =>
              mtrace on .zero with s!"[injectivityOrNoConfusionOrLeave] injetivity aplication failed"
              k false .nil .nil st
          else
            mtrace on .zero with s!"[injectivityOrNoConfusionOrLeave] no injectivity theorem found, skipping"
            k false .nil .nil st
        else
          mtrace on .zero with s!"[injectivityOrNoConfusionOrLeave] different index"
          -- let (goalI,goalE) := st.introTree.topGoalForForwId target_forw_id
          let ugn := if st.uNodes.binSearchContains target_forw_id (· < ·) then unode target_forw_id else gnode target_forw_id
          let u ← getLevel goalE -- ↓ as in `Lean.Meta.mkNoConfusion`
          let term := mkAppN (mkConst (Name.mkStr v.name "noConfusion") (u :: us)) (T.getAppArgs ++ #[goalE, l, r, .fvar ⟨ugn⟩ ])
          if !(← isTypeCorrect term)
          then
            mtrace on .zero with s!"[injectivityOrNoConfusionOrLeave] term not correct {← ppExpr term}"
            k false .nil .nil st
          else
            let ty ← inferType term
            if (← defEqWiMv ty goalE).isNone
            then
              mtrace on .zero with s!"[injectivityOrNoConfusionOrLeave] term correct but types not defeq ..."
              k false .nil .nil st
            else
              mtrace on .zero with s!"[injectivityOrNoConfusionOrLeave] integrating term {← ppExpr term} at goalId {goalI}"
              integrateBackwardStd
                revCountMax goalI term (.string s!"[Exfalso] forw {target_forw_id} goal {goalI}") 0 .nil .nil st
                <| fun newI newG st => k true newI newG st
