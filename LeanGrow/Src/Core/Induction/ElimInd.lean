
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrowBeta.Utils.LeanGrow.Expr
import LeanGrowBeta.Core.Induction.Format
import LeanGrowBeta.Utils.Lean.Generalize
import LeanGrowBeta.Utils.Lean.Revert
import LeanGrowBeta.Utils.Lean.MetaAPI

open Lean Meta


/--
- May have to fix reverted tnodes to become args in backstep !
-/
@[specialize, inline]
partial def elimInductionMain
  (revert : MVarId → Array FVarId → LocalContext → LocalInstances → MetaM (Array FVarId × MVarId))
  (l1 : LocalContext) (l2 : LocalInstances)
  (backIdx : Nat) (goal : Expr) (target : FVarId)
  (recu : RecursorCache)
  : MetaM (Prod3 (OptionProd Expr Nat) LocalContext LocalInstances) :=
  withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
    loadRecursorCache l1 l2 recu
    -- *Note** this ensures mvars of recus come loaded with the current context !
    let h := recu.motArgMv
    let H ← instantiateMVars (h[h.size - 1]!)
    let t := (.fvar target)
    mtrace on .zero with s!"[elimInductionMain] defeq mvar-fvar of types: {← ppExpr (← inferType H)} vs. {← ppExpr (← inferType t)}"
    if !(← defEqWiMvNoClear H t l1 l2).isSome
    then
      mtrace on .zero with s!"[elimInductionMain] defeq failed"
      return ⟨.none,l1,l2⟩
    else
      let h := (← h.mapM (instantiateMVars))
      mtrace on .zero with s!"[elimInductionMain] propagation to remaining mtive args : {← h.mapM ppExpr}"
      if h.any (fun | .fvar fid => fid.isUnode | _ => true) -- we don't expect worker fvars or tnodes if `t`,
      -- which we expect to be the unique dependency sink of the arguements, wasn't one
      then
        return ⟨.none,l1,l2⟩
      else
        let relevant := h.map Expr.fvarId!
        let rec prohib (l1 : LocalContext) (l2 : LocalInstances) (e : List Expr) : MetaM Bool := do
          match e with
          | [] =>
              return false
          | e :: es =>
              let T ← InferType e l1 l2
              match T.getFVars with
              | [] => prohib l1 l2 es
              | fvs =>
                  let mut dep? := false
                  let mut nx := []
                  for fv in fvs do
                    if target == fv.fvarId!
                    then
                      dep? := true
                      break
                    else
                      if es.contains fv
                      then
                        continue
                      else
                        nx := fv :: nx
                  if dep?
                  then
                    return true
                  else
                    prohib l1 l2 (nx ++ es)
        match ← generalizeTnodesSafeIgnoring l1 l2 goal (fun _ _ _ => return false) (fun e l1 l2 => prohib l1 l2 [e]) (fun _ _ _ => return true) with
        | .none => return ⟨.none,l1,l2⟩
        | .some goal revTnodes => do
            mtrace on .zero with s!"[elimInductionMain] generalised tnodes {← revTnodes.mapM ppExpr} to new goal {← ppExpr goal}"
            -- *Note* we're using the "safe" version that fails if the goal contains type-typed tnodes depending on the `targets`
            -- Simply checking if the goal has such tnodes isn't enough : the prop-typed one can depend on type-typed ones
            let mvarId ← mkFreshExprMVarAt l1 l2 (goal)
            let (allRev, mvarId) ← revert mvarId.mvarId! relevant l1 l2
              -- *Note* we expect `relevant` to be sorted wrt. dependecies ; this is a property : they are in the order of
              -- the motive of the principle, which wouldn't be type correct if they weren't ordered
            mtrace on .zero with s!"[elimInductionMain] reverted fvars {repr allRev} to new goal {← ppExpr (← mvarId.getType)}"
            let allRevFirst := ((allRev.take relevant.size).map Expr.fvar).filter (fun | .fvar x => !(x.isUnode) | _ => false)
            -- **Note* ↑↓ `instantiateForall` actually uses whnf, so will reduce lets !
            -- We crutially assume that `revert` reverts unused lets also !!
            let revgoal ← instantiateForall (← mvarId.getType) allRevFirst
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
                if ← isTypeCorrect proof
                then
                  return ⟨.some proof tnodeRange,l1,l2⟩
                else
                  mtrace on .zero with s!"[elimInductionMain] incorrect proofterm"
                  return ⟨.none,l1,l2⟩
            else
              mtrace on .zero with s!"[elimInductionMain] defeq failed"
              return ⟨.none,l1,l2⟩



@[specialize, inline]
def elimInductionComp
  (introAdmissible? : Nat → Bool) (sinkRevCutOff : Nat)
  (l1 : LocalContext) (l2 : LocalInstances)
  (backIdx : Nat) (goal : Expr) (targets : FVarId)
  (recu : RecursorCache)
  : MetaM (Prod3 (OptionProd Expr Nat) LocalContext LocalInstances) :=
  elimInductionMain (fun g fv l1 l2 => MVarId.revert_NoTn_cutOff introAdmissible? l1 l2 g fv sinkRevCutOff) l1 l2 backIdx goal targets recu

@[specialize, inline]
def elimInductionData
  (introAdmissible? : Nat → Bool) (depsCache : Array (List LocalDecl)) (workerDepsCache : Array (FVarId × (List LocalDecl)))  (sinkRevCutOff : Nat)
  (l1 : LocalContext) (l2 : LocalInstances)
  (backIdx : Nat) (goal : Expr) (targets : FVarId)
  (recu : RecursorCache)
  : MetaM (Prod3 (OptionProd Expr Nat) LocalContext LocalInstances) :=
  elimInductionMain (fun g fv l1 l2 => MVarId.revert_NoTn_cutOff_wDepsCache introAdmissible? l1 l2 g fv depsCache workerDepsCache sinkRevCutOff) l1 l2 backIdx goal targets recu
