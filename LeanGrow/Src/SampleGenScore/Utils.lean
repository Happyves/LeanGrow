
/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Utils.Tracing
import LeanGrow.Src.Data.CTrie.Operations
import LeanGrow.Src.Utils.Lean.LocalContext
import LeanGrow.Src.SampleGenScore.Types
import LeanGrow.Src.Utils.Lean.MetaAPI



open Lean Meta


@[inline, specialize]
def Lean.Expr.withRelevantArgsBack (l1 : LocalContext) (l2 : LocalInstances)
  (head : Expr) (args : Array Expr)
  {α : Sort _} (init : α) (f : Expr → α → MetaM α) : MetaM α :=
  do
  mtracing
  withLCtx l1 l2 <| do
    if args.isEmpty
    then
      return init
    else
      let finfo ← getFunInfo head
      let .mk res _ ← finfo.paramInfo.foldlM (fun (st,i) pinfo => do
        if i ≥ args.size -- partial applications
        then return (st, i+1)
        else
          match pinfo.binderInfo with
          | .default =>
              if pinfo.hasFwdDeps -- contains goal deps
              then
                mtrace on .zero with s!"[withRelevantArgsBack] skip {i} of type {← ppExpr <| ← inferType args[i]!}"
                return (st, i+1)
              else
                -- assumes users added instane param with correct binder
                let Arg := args[i]!
                mtrace on .zero with s!"[withRelevantArgsBack] add {i} of type {← ppExpr <| ← inferType args[i]!}"
                let st ← f Arg st
                return (st, i+1)

          | _ =>
              mtrace on .zero with s!"[withRelevantArgsBack] skip {i} of type {← ppExpr <| ← inferType args[i]!}"
              return (st, i+1)
        ) (init,0)
      return res


@[inline]
def Lean.Expr.getRelevantArgsBack (l1 : LocalContext) (l2 : LocalInstances) (e : Expr) : MetaM (Array Expr) :=
  let head := e.getAppFn
  let args := e.getAppArgs
  head.withRelevantArgsBack l1 l2 args (Array.emptyWithCapacity 6) (fun x A => return A.push x)


@[inline, specialize]
def Lean.Expr.withRelevantArgsForw (l1 : LocalContext) (l2 : LocalInstances)
  (head : Expr) (args : Array Expr)
  {α : Sort _} (init : α) (f : Expr → α → MetaM α) : MetaM α :=
  withLCtx l1 l2 <| do
    do
    if args.isEmpty
    then
      return init
    else
      let finfo ← getFunInfo head
      let .mk res _ := finfo.paramInfo.foldl (fun (st,i) pinfo =>
        if i ≥ args.size -- partial applications
        then (st, i+1)
        else
          match pinfo.binderInfo with
          | .default =>
              ((st.filter (fun n => !(pinfo.backDeps.contains n))).push i, i+1)
          | _ =>
              (st, i+1)
        ) (#[],0)
      res.foldlM (fun S i => f args[i]! S) init


@[inline]
def Lean.Expr.getRelevantArgsForw (l1 : LocalContext) (l2 : LocalInstances) (e : Expr) : MetaM (Array Expr) :=
  let head := e.getAppFn
  let args := e.getAppArgs
  head.withRelevantArgsBack l1 l2 args (Array.emptyWithCapacity 6) (fun x A => return A.push x)


#check List.getElem_cons_zero
-- explicit binded args can still be implicit ..

/-
Test to check if `hasFwdDeps` contains goal deps
```
def test (n : Nat) : Fin (n+1) := ⟨0,by grind⟩

run_meta do
  let finfo ← getFunInfo (.const `test [])
  let res := finfo.paramInfo[0]!.hasFwdDeps
  IO.println res
```

-/


partial def Lean.Expr.isPseudoAtomic (l1 : LocalContext) (l2 : LocalInstances) : Expr → MetaM Bool
  | .lam .. | .forallE .. => return false
  | .letE _ _ V B _ => (B.instantiate1 V).isPseudoAtomic l1 l2
  | e@(.app ..) => do
      if ← e.getAppFn.isPseudoAtomic l1 l2
      then
        let as ← e.getRelevantArgsBack l1 l2
        return as.all Expr.isAtomic
        --as.allM (Lean.Expr.isPseudoAtomic l1 l2)
        -- too strong
      else
        return false
  | .proj _ _ e | .mdata _ e => e.isPseudoAtomic l1 l2
  | _ => return true


partial def Lean.Expr.pseudoConst (l1 : LocalContext) (l2 : LocalInstances) : Expr → MetaM (Option Name)
  | .lam .. | .forallE .. => return .none
  | .letE _ _ V B _ => (B.instantiate1 V).pseudoConst l1 l2
  | e@(.app ..) => do
      match ← e.getAppFn.pseudoConst l1 l2 with
      | R@(.some _) =>
        let as ← e.getRelevantArgsBack l1 l2
        if as.all Expr.isAtomic --← as.allM (Lean.Expr.isPseudoAtomic l1 l2)
        then return R
        else return .none
      | R =>
        return R
  | .proj _ _ e | .mdata _ e => e.pseudoConst l1 l2
  | .const n _ => return .some n
  | _ => return .none


def mathlibTactic? : Name → Bool
  | .str .anonymous s1 =>
    s1 == "Lean" -- Lean.Omega for example
  | .str (.str .anonymous s1) s2 =>
    (s1 == "Mathlib" && s2 == "Tactic") || s1 == "Lean"
  -- todo : Batteries ?
  | .str p _ =>
    mathlibTactic? p
  | .num p _ =>
     mathlibTactic? p
  | .anonymous =>
    false



def Lean.Name.getPrefix! : Name → String
  | anonymous => "anonymous"
  | str .anonymous p => p
  | num p _   => p.getPrefix!
  | str p _   => p.getPrefix!

@[inline]
def Lean.Name.isRefl? (h : Name) : Bool :=
  (h == ``Eq.refl || h == ``Iff.refl || h == ``Iff.rfl || h == ``rfl)


@[inline]
def Lean.Name.badSample? (sn : Name) : Bool :=
  (sn.getPrefix! == "_private") || sn.isRefl?



@[inline]
partial def Lean.Expr.shollowTestProhibit (e : Expr)  : Bool :=
  let rec go (fuel : Nat) : List Expr → Bool
    | [] => false
    | e :: more =>
      if fuel = 0
      then false
      else
        let nope? :=
          match e with
          | .const n _ => mathlibTactic? n
          | _ => false
        if nope?
        then true
        else
          match e with
          | .app .. =>
            let rec foldPar (m : List Expr) : Expr → List Expr
              | .app l r =>  foldPar (r :: m) l
              | e => e :: m
            go (fuel-1) (foldPar more e)
          | .lam _ l r _ => go (fuel-1) (l :: r :: more)
          | .forallE _ l r _ => go (fuel-1) (l :: r :: more)
          | .letE _ l r z _ => go (fuel-1) (l :: r :: z :: more)
          | .proj _ _ e => go (fuel-1) (e :: more)
          | .mdata _ e => go (fuel-1) (e :: more)
          | _ => go (fuel-1) more
  go 32 [e]


#check Lean.Omega.LinearCombo.sub_eval

-- #eval mathlibTactic? `Lean.Omega.LinearCombo.sub_eval
