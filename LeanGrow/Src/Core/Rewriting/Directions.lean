/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Utils.Lean.Expr.Basic
import LeanGrow.Src.Utils.LeanGrow.Nodes

open Lean

inductive rwDirs where
| no | yes
| ap (_ : rwDirs) (_ : rwDirs)
| la (_ : rwDirs) (_ : rwDirs)
| al (_ : rwDirs) (_ : rwDirs)
| le (_ : rwDirs) (_ : rwDirs) (_ : rwDirs)
| pro (_ : rwDirs)
deriving BEq, Inhabited, Repr



structure DirsAppFn where
  head : Expr
  hdirs : rwDirs
  args : Array Expr
  argsdirs :  Array rwDirs
deriving BEq, Inhabited, Repr



partial def rwDirs.getAppFnArgs (ds : rwDirs) (ref : Expr): DirsAppFn :=
  let rec goBot (asd : Array rwDirs) (as : Array Expr) : Expr → DirsAppFn
    | .app l r => goBot (asd.push .no) (as.push r) l
    | .mdata _ e => goBot asd as e
    | x => ⟨x, .no, as.reverse, asd.reverse⟩
  let rec goTop (asd : Array rwDirs) (as : Array Expr) : rwDirs → Expr → DirsAppFn
    | x, .mdata _ e => goTop asd as x e
    | .ap l r, .app L R =>
      if l == .no
      then goBot (asd.push r) (as.push R) L
      else goTop (asd.push r) (as.push R) l L
    | x, y => ⟨y, x, as.reverse, asd.reverse⟩
  goTop #[] #[] ds ref



partial def rwDirs.getAppArgs (ds : rwDirs) (ref : Expr): Array Expr × Array rwDirs :=
  let rec goBot (asd : Array rwDirs) (as : Array Expr) : Expr → Array Expr × Array rwDirs
    | .app l r => goBot (asd.push .no) (as.push r) l
    | .mdata _ e => goBot asd as e
    | _ => ⟨as.reverse, asd.reverse⟩
  let rec goTop (asd : Array rwDirs) (as : Array Expr) : rwDirs → Expr → Array Expr × Array rwDirs
    | x, .mdata _ e => goTop asd as x e
    | .ap l r, .app L R =>
      if l == .no
      then goBot (asd.push r) (as.push R) L
      else goTop (asd.push r) (as.push R) l L
    | _, _ => ⟨as.reverse, asd.reverse⟩
  goTop #[] #[] ds ref


partial def rwDirs.getBinders (dirs : rwDirs) (e : Expr) : ListProd rwDirs Expr :=
  let rec go (out : ListProd rwDirs Expr) : ListProd rwDirs Expr → ListProd rwDirs Expr
    | .nil => out
    | .cons d e more =>
      match d , e with
      | _, .mdata _ e => go out <| .cons d e more
      | .ap l r, .app L R => go out (.cons l L <| .cons r R more)
      | .la .., .lam ..  | .al .., .forallE .. | .le .., .letE .. => go (.cons d e out) more
      | .pro d, .proj _ _  e => go out (.cons d e out)
      | _, _ => go out more
  go .nil <| .cons dirs e .nil


@[specialize]
partial def lambdaLetAllBoundedTelescopeWorkerDirsDeps
  (l1 : LocalContext) (l2 : LocalInstances)
  (type : Expr) (sofarFvs : Array Expr) (workerDeps : Array (FVarId × (List FVarId)))  (d D : Nat) (dirs : rwDirs)
  : MetaM (Prod6 Expr rwDirs (Array Expr) (Array (FVarId × (List FVarId))) LocalContext LocalInstances) := do
  if d < D
  then
    match type, dirs with
    | .lam _ t b _, .la _ r | .forallE _ t b _, .al _ r =>
        let w ← worker d
        let ⟨wfv,b,l1,l2⟩ ← withFreeing w t b l1 l2
        let fvst := t.getFVarIds--.mapM (FVarId.GetDecl · l1 l2)
        lambdaLetAllBoundedTelescopeWorkerDirsDeps l1 l2 b (sofarFvs.push (.fvar wfv)) (workerDeps.push (wfv,fvst)) (d+1) D r
    | .letE _ t v b _, .le _ _ z =>
        let w ← worker d
        let ⟨wfv,b,l1,l2⟩ ← withFreeingLet w t v b l1 l2
        let fvst := v.getFVarIds--.mapM (FVarId.GetDecl · l1 l2)
        lambdaLetAllBoundedTelescopeWorkerDirsDeps l1 l2 b (sofarFvs.push (.fvar wfv)) (workerDeps.push (wfv,fvst)) (d+1) D z
    | _, _ => return ⟨type, dirs, sofarFvs, workerDeps, l1,l2⟩
  else
    return ⟨type, dirs, sofarFvs, workerDeps, l1,l2⟩
