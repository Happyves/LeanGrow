
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Utils.LeanGrow.Expr
import LeanGrow.Src.Core.Induction.Format
import LeanGrow.Src.Utils.Lean.Generalize
import LeanGrow.Src.Utils.Lean.Revert
import LeanGrow.Src.Utils.Lean.MetaAPI

open Lean Meta

/--
- May have to fix reverted tnodes to become args in backstep !
-/
@[specialize, inline]
partial def functionalInductionMain
  (introAdmissible? : Nat → Bool) (sinkRevCutOff : Nat) (depsCache : Array DepCache)
  (l1 : LocalContext) (l2 : LocalInstances)
  (backIdx : Nat) (goal : Expr) (targets : Array FVarId)
  (recu : FunRecursorCache)
  : MetaM (Prod3 (OptionProd Expr Nat) LocalContext LocalInstances) :=
  withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
    mtracing
    loadFunRecursorCache l1 l2 recu
    -- *Note** this ensures mvars of recus come loaded with the current context !
    let h := recu.motArgMv
    let mut failed := false
    for i in [:h.size] do
      let H ← instantiateMVars (h[h.size - 1 - i]!)
      let t ← instantiateMVars (.fvar (targets[targets.size - 1 - i]!))
      mtrace on .zero with s!"[functionalInductionMain] defeq mvar-fvar {H} vs {t} of types: {← ppExpr (← inferType H)} vs. {← ppExpr (← inferType t)}"
      mtrace on .one with s!"[functionalInductionMain] defeq mvar-fvar of types: {repr (← inferType H)} vs. {repr (← inferType t)}}"
      mtrace on .two with s!"[functionalInductionMain]\n{← printMetaMContextDecls_1}"
      mtrace on .two with s!"[functionalInductionMain]\n{← printMetaDecls}"
      if (← defEqWiMvNoClear H t l1 l2).isSome
      then
        continue
      else
        mtrace on .zero with s!"[functionalInductionMain] defeq failed"
        failed := true
        break
    if failed
    then
      clearMvarAssignments
      return ⟨.none,l1,l2⟩
    else
      let relevant := targets
      let .mk gen revTnodes l1 l2 ← generalizeTnodesSafeIgnoring l1 l2 goal #[] (fun _ _ _ => return false)
        match gen with
        | .none =>
          clearMvarAssignments
          return ⟨.none,l1,l2⟩
        | .some goal => do
            mtrace on .zero with s!"[elimInductionMain] generalised tnodes {← revTnodes.mapM ppExpr} to new goal {← ppExpr goal}"
            if !goal.hasTnodes
            then
              mtrace on .zero with s!"[functionalInductionMain] generalised tnodes {← revTnodes.mapM ppExpr} to new goal {← ppExpr goal}"
              -- *Note* we're using the "safe" version that fails if the goal contains type-typed tnodes depending on the `targets`
              -- Simply checking if the goal has such tnodes isn't enough : the prop-typed one can depend on type-typed ones
              let .mk revgoal _ allRev l1 l2 ← revert_NoTn_cutOff_wDepsCache introAdmissible? l1 l2 goal relevant depsCache #[] sinkRevCutOff
                -- *Note* we expect `relevant` to be sorted wrt. dependecies ; this is a property : they are in the order of
                -- the function application, which wouldn't be type correct if they weren't ordered
              mtrace on .zero with s!"[functionalInductionMain] reverted fvars {repr allRev} to new goal {← ppExpr revgoal}"
              let allRevFirst := ((allRev.take relevant.size).map Expr.fvar).filter (fun | .fvar x => !(x.isUnode) | _ => false)
              -- **Note* ↑↓ `instantiateForall` actually uses whnf, so will reduce lets !
              -- We crutially assume that `revert` reverts unused lets also !!
              let revgoal ← instantiateForall revgoal allRevFirst
              let motive ← mkLambdaFVars allRevFirst revgoal
              mtrace on .zero with s!"[functionalInductionMain] defeq for motive of types: {← ppExpr (← inferType (← instantiateMVars motive))} vs. {← ppExpr (← inferType (← instantiateMVars recu.motMv))}"
              if (← defEqWiMvNoClear (← instantiateMVars motive) (← instantiateMVars recu.motMv) l1 l2).isSome
              then
                mtrace on .zero with s!"[functionalInductionMain] defeq succeeded"
                let ⟨trafoArgs , ⟨_,_,tnodeRange⟩, l1,l2⟩ ← instantiateOrTnodifyMVarsMulti backIdx recu.recuArgMv l1 l2 {}
                withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
                  mtrace on .zero with s!"[functionalInductionMain] recuArgsMV {← recu.recuArgMv.mapM ppExpr} trafoArgs {← trafoArgs.mapM ppExpr}"
                  let allRevFinal := ((allRev.drop relevant.size).map Expr.fvar).filter (fun | .fvar x => !(x.isUnode) | _ => false)
                  let proof ← instantiateMVars (mkAppN (mkAppN (mkAppN recu.term trafoArgs) allRevFinal) revTnodes)
                    -- *Note* we have to instantiate to get `recu.term` level mvars to be instantiated
                  mtrace on .zero with s!"[functionalInductionMain] final proofterm {← ppExpr proof}"
                  clearMvarAssignments
                  if ← isTypeCorrect proof
                  then
                    return ⟨.some proof tnodeRange,l1,l2⟩
                  else
                    mtrace on .zero with s!"[functionalInductionMain] incorrect proofterm"
                    return ⟨.none,l1,l2⟩
              else
                mtrace on .zero with s!"[functionalInductionMain] defeq failed"
                return ⟨.none,l1,l2⟩
            else
              mtrace on .zero with s!"[functionalInductionMain] bad tnodes"
              return ⟨.none,l1,l2⟩
