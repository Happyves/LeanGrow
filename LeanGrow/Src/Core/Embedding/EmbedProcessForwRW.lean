
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Core.Embedding.EmbedQueryForwRW
import LeanGrow.Src.Core.Rewriting.Main


open Lean Meta



/-- Forward rw just for rws with all sinks in goal-/
@[inline]
def embedForwRWProcess (l1 : LocalContext) (l2 : LocalInstances)
  (thmData : ThmFormat) (res : embedForwRWData)
  {α : Sort _} (fail : MetaM α) (k : Expr → List Nat → MetaM α) : MetaM α := do
  do
  mtracing
  -- *Note*, we expect the defeqs to have assigned transitive dependet arguments
  let arg_lvls : Array Level := Array.replicate thmData.lvlParamsNum .zero
  let arg_exprs : Array Expr := Array.replicate thmData.hypsNum (failExpr "")
  let (arg_lvls, todo_lvls) := res.llv.foldl (arg_lvls, List.range thmData.lvlParamsNum)
    (fun pos al (arg_lvls, todo_lvls) =>
      let arg_lvls := arg_lvls.set! pos al
      let todo_lvls := List.orderedEraseOrLeave pos todo_lvls
      (arg_lvls, todo_lvls))
  if !(todo_lvls.isEmpty)
  then
    mtrace on .zero with s!"[embedForwRWProcess] aboring due to none empty todo_lvls: {todo_lvls}"
    fail
  else
    mtrace on .zero with s!"[embedForwRWProcess] arg_lvls {repr arg_lvls}"
    let (arg_exprs, todo_expr_inds) := res.ln.foldl (arg_exprs, List.range thmData.hypsNum)
      (fun pos al (arg_exprs, todo_expr_inds) =>
        let arg_exprs := arg_exprs.set! pos al
        let todo_expr_inds := List.orderedEraseOrLeave pos todo_expr_inds
        (arg_exprs, todo_expr_inds))
    mtrace on .zero with s!"[embedForwRWProcess] arg_exprs {← arg_exprs.mapM ppExpr}, todo_expr_inds {todo_expr_inds}"
    todo_expr_inds.foldlMcps (arg_exprs,todo_expr_inds) (fun i (arg_exprs,todo_expr_inds) cont => do
      let T := thmData.hypsTypes[i]!
      mtrace on .zero with s!"[embedForwRWProcess] todo type {← ppExpr T}"
      let T := T.onAllSubtermsTR (fun
        | x@(.mvar ⟨.num _ p⟩) =>
            if todo_expr_inds.orderedContains p
            then x
            else arg_exprs[p]!
        | .sort lv => .sort <| lv.onAllSubtermsTR (fun
            | x@(.mvar ⟨.num _ p⟩) =>
                if todo_lvls.orderedContains p
                then x
                else arg_lvls[p]!
            | x => x)
        | .const n lvs => .const n  <| lvs.map <| fun lv => lv.onAllSubtermsTR (fun
            | x@(.mvar ⟨.num _ p⟩) =>
                if todo_lvls.orderedContains p
                then x
                else arg_lvls[p]!
            | x => x)
        | x => x)
      mtrace on .zero with s!"[embedForwRWProcess] instantaited to {← ppExpr T}"
      match thmData.hyps[i]! with
      | .reg .. =>
          mtrace on .zero with s!"[embedForwRWProcess] unassigned arg {i}, aborting "
          fail
      | .inst .. =>
          let val? ← SynthInstance T l1 l2
          match val? with
          | .none =>
              mtrace on .zero with s!"[embedForwRWProcess] ways instance, but synthesis failed"
              fail
          | .some val =>
              mtrace on .zero with s!"[embedForwRWProcess] successfully synthesised instance for it"
              cont (arg_exprs.set! i val, todo_expr_inds.orderedEraseOrLeave i)
      ) <| fun (arg_exprs,_) => do
          let term := mkAppN (match thmData.name with | .inl n =>(.const n arg_lvls.toList) | .inr fv => .fvar fv) arg_exprs
          let GUinds := term.getGUFVarsIds.mapTRR (fun | ⟨.num _ i⟩ => i | _ => 42)
          mtrace on .zero with s!"[embedForwIncludePostProcess] term {← ppExpr term} of type {← ppExpr (← inferType term)}"
          mtrace on .zero with s!"[embedForwIncludePostProcess] GUinds {GUinds}"
          k term GUinds

#check 1




@[specialize, inline]
def embedForwRWPreIntegrate
  (introAdmissible? : Nat → Bool) (depsCache : Array DepCache) (RevCutOff : Nat)
  (l1 : LocalContext) (l2 : LocalInstances)
  (dirs : rwDirs) (within : Expr) (thmData : ThmFormat)
  (rwableFvar term : Expr)
  {α : Sort _} (fail : LocalContext → LocalInstances → MetaM α) (k : Expr → LocalContext → LocalInstances → MetaM α) : MetaM α :=
  match thmData with
  | .std .. => throwError s!"[embedForwRWPreIntegrate] tryto to perform rewrite with non rewrite lemm {repr thmData.name}"
  | .rw _ _ kind .. => do
      withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
        let prefixed : Expr := ← do
          match kind with
          | .eq_mp => return term
          | .eq_mpr => mkAppM `Eq.symm #[term]
          | .iff_mp => mkAppM `propext #[term]
          | .iff_mpr => mkAppM `Eq.symm #[← mkAppM `propext #[term]]
        let T ← InferType prefixed l1 l2
        let .some (_,pat,_) := T.eq? | throwError s!"[embedForwRWPreIntegrate] expected eq, got {← ppExpr T}"
        let ⟨fullProof,l1,l2⟩ ← mainForwRW introAdmissible? depsCache RevCutOff l1 l2 dirs rwableFvar within pat prefixed
        match fullProof with
        | .some fullProof =>
          if ← IsTypeCorrect fullProof l1 l2
          then k fullProof l1 l2
          else fail l1 l2
        | _ => fail l1 l2
