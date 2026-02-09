
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
partial def elimInductionMain
  (introAdmissible? : Nat → Bool) (sinkRevCutOff : Nat) (depsCache : Array DepCache)
  (l1 : LocalContext) (l2 : LocalInstances)
  (backIdx : Nat) (goal : Expr) (target : FVarId)
  (recu : RecursorCache)
  : MetaM (Prod3 (OptionProd Expr Nat) LocalContext LocalInstances) :=
  withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
    mtracing
    loadRecursorCache l1 l2 recu
    -- *Note** this ensures mvars of recus come loaded with the current context !
    let h := recu.motArgMv
    if h.size > 1
    then
      mtrace on .zero with s!"[elimInductionMain] elim with more then one major arg, not supported yet"
      return ⟨.none,l1,l2⟩
    else
      let H ← instantiateMVars (h[h.size - 1]!)
      let t := (.fvar target)
      mtrace on .zero with s!"[elimInductionMain] defeq mvar-fvar of types: {← ppExpr (← inferType H)} vs. {← ppExpr (← inferType t)}"
      if !(← defEqWiMvNoClear H t l1 l2).isSome
      then
        mtrace on .zero with s!"[elimInductionMain] defeq failed"
        clearMvarAssignments
        return ⟨.none,l1,l2⟩
      else
        let h := (← h.mapM (instantiateMVars))
        mtrace on .zero with s!"[elimInductionMain] propagation to remaining mtive args : {← h.mapM ppExpr}"
        clearMvarAssignments
        if h.any (fun | .fvar fid => fid.isUnode | _ => true) -- we don't expect worker fvars or tnodes if `t`,
        -- which we expect to be the unique dependency sink of the arguements, wasn't one
        then
          return ⟨.none,l1,l2⟩
        else
          let relevant := h.map Expr.fvarId!
          let .mk gen revTnodes l1 l2 ← generalizeTnodesSafeIgnoring l1 l2 goal #[] (fun _ _ _ => return false)
          match gen with
          | .none => return ⟨.none,l1,l2⟩
          | .some goal => do
              mtrace on .zero with s!"[elimInductionMain] generalised tnodes {← revTnodes.mapM ppExpr} to new goal {← ppExpr goal}"
              if !goal.hasTnodes
              then
                let .mk revgoal _ allRev l1 l2 ← revert_NoTn_cutOff_wDepsCache introAdmissible? l1 l2 goal relevant depsCache #[] sinkRevCutOff
                  -- *Note* we expect `relevant` to be sorted wrt. dependecies ; this is a property : they are in the order of
                  -- the motive of the principle, which wouldn't be type correct if they weren't ordered
                mtrace on .zero with s!"[elimInductionMain] reverted fvars {repr allRev} to new goal {← ppExpr revgoal}"
                let allRevFirst := ((allRev.take relevant.size).map Expr.fvar).filter (fun | .fvar x => !(x.isUnode) | _ => false)
                -- **Note* ↑↓ `instantiateForall` actually uses whnf, so will reduce lets !
                -- We crutially assume that `revert` reverts unused lets also !!
                let revgoal ← instantiateForall revgoal allRevFirst
                let motive ← mkLambdaFVars allRevFirst revgoal
                  mtrace on .zero with s!"[elimInductionMain] made motive  {← ppExpr (← instantiateMVars motive)}"
                mtrace on .zero with s!"[elimInductionMain] defeq for motive of types: {← ppExpr (← inferType (← instantiateMVars motive))} vs. {← ppExpr (← inferType (← instantiateMVars recu.motMv))}"
                if (← (defEqWiMvNoClear (← InstantiateMVars motive l1 l2) (← InstantiateMVars recu.motMv l1 l2) l1 l2)).isSome
                then
                  mtrace on .zero with s!"[elimInductionMain] defeq succeeded"
                  let ⟨trafoArgs , ⟨_,_,tnodeRange⟩, l1,l2⟩ ←  instantiateOrTnodifyMVarsMulti backIdx recu.recuArgMv l1 l2 {}
                  withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
                    let allRevFinal := ((allRev.drop relevant.size).map Expr.fvar).filter (fun | .fvar x => !(x.isUnode) | _ => false)
                    let proof ← instantiateMVars (mkAppN (mkAppN (mkAppN recu.term trafoArgs) allRevFinal) revTnodes)
                      -- *Note* we have to instantiate to get `recu.term` level mvars to be instantiated
                    mtrace on .zero with s!"[elimInductionMain] final proofterm {← ppExpr proof}"
                    mtrace on .one with s!"[elimInductionMain] trafoArgs {← trafoArgs.mapM ppExpr} of types {← trafoArgs.mapM (fun x => return ← ppExpr (← inferType x))}"
                    clearMvarAssignments
                    if ← isTypeCorrect proof
                    then
                      return ⟨.some proof tnodeRange,l1,l2⟩
                    else
                      mtrace on .zero with s!"[elimInductionMain] incorrect proofterm"
                      return ⟨.none,l1,l2⟩
                else
                  mtrace on .zero with s!"[elimInductionMain] defeq failed"
                  return ⟨.none,l1,l2⟩
              else
                mtrace on .zero with s!"[elimInductionMain] bad tnodes"
                return ⟨.none,l1,l2⟩



#check revert_NoTn_cutOff_wDepsCache
