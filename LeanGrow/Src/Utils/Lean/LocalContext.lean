
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Lean.Meta.Basic
import Batteries.Tactic.OpenPrivate
import LeanGrowBeta.Data.Amalgames
import LeanGrowBeta.Utils.LeanGrow.Nodes

set_option autoImplicit true

open Lean Meta

open private Lean.Meta.withLocalDeclImp from Lean.Meta.Basic
open private Lean.Meta.isClassQuick? from Lean.Meta.Basic
open private Lean.Meta.isClassExpensive? from Lean.Meta.Basic



-- # Add declarations

@[inline]
def withNonInstLocalDecl (n : Name) (type : Expr) (init : LocalContext) : FVarId × LocalContext :=
  let fv := ⟨n⟩
  (fv, init.mkLocalDecl fv n type .default .default)

@[inline]
def withNonInstLetDecl (n : Name) (type value: Expr) (init : LocalContext) : FVarId × LocalContext :=
  let fv := ⟨n⟩
  (fv, init.mkLetDecl fv n type value false .default)

@[inline]
def WithLocalDecl (n : Name) (type : Expr) (initD : LocalContext) (initI : LocalInstances) : MetaM (Prod3 FVarId LocalContext LocalInstances) :=
  let fv := ⟨n⟩
  let ltx := initD.mkLocalDecl fv n type .default .default
  withReader (fun ctx => {ctx with lctx := ltx, localInstances := initI}) do
    match (← Lean.Meta.isClassQuick? type) with
    | .none   => return ⟨fv,ltx,initI⟩
    | .some c => return ⟨fv,ltx, (initI.push {className := c, fvar := .fvar fv})⟩
    | .undef  =>
        match (← Lean.Meta.isClassExpensive? type) with
        | .none  => return ⟨fv,ltx,initI⟩
        | .some c => return ⟨fv,ltx, (initI.push {className := c, fvar := .fvar fv})⟩

@[inline]
def WithLetDecl (n : Name) (type value : Expr) (initD : LocalContext) (initI : LocalInstances) : MetaM (Prod3 FVarId LocalContext LocalInstances) :=
  let fv := ⟨n⟩
  let ltx := initD.mkLetDecl fv n type value false .default
  withReader (fun ctx => {ctx with lctx := ltx, localInstances := initI}) do
    match (← Lean.Meta.isClassQuick? type) with
    | .none   => return ⟨fv,ltx,initI⟩
    | .some c => return ⟨fv,ltx, (initI.push {className := c, fvar := .fvar fv})⟩
    | .undef  =>
        match (← Lean.Meta.isClassExpensive? type) with
        | .none  => return ⟨fv,ltx,initI⟩
        | .some c => return ⟨fv,ltx, (initI.push {className := c, fvar := .fvar fv})⟩

@[inline]
def withNonInstLocalDeclU (n : Name) (type : Expr) (init : LocalContext) : MetaM (FVarId × LocalContext) := do
  let fv ← mkFreshFVarId
  return (fv, init.mkLocalDecl fv n type .default .default)

@[inline]
def withNonInstLetDeclU (n : Name) (type value: Expr) (init : LocalContext) : MetaM (FVarId × LocalContext) := do
  let fv ← mkFreshFVarId
  return (fv, init.mkLetDecl fv n type value false .default)

@[inline]
def WithLocalDeclU (n : Name) (type : Expr) (initD : LocalContext) (initI : LocalInstances) : MetaM (Prod3 FVarId LocalContext LocalInstances) := do
  let fv ← mkFreshFVarId
  let ltx := initD.mkLocalDecl fv n type .default .default
  withReader (fun ctx => {ctx with lctx := ltx, localInstances := initI}) do
    match (← Lean.Meta.isClassQuick? type) with
    | .none   => return ⟨fv,ltx,initI⟩
    | .some c => return ⟨fv,ltx, (initI.push {className := c, fvar := .fvar fv})⟩
    | .undef  =>
        match (← Lean.Meta.isClassExpensive? type) with
        | .none  => return ⟨fv,ltx,initI⟩
        | .some c => return ⟨fv,ltx, (initI.push {className := c, fvar := .fvar fv})⟩

@[inline]
def WithLetDeclU (n : Name) (type value : Expr) (initD : LocalContext) (initI : LocalInstances) : MetaM (Prod3 FVarId LocalContext LocalInstances) := do
  let fv ← mkFreshFVarId
  let ltx := initD.mkLetDecl fv n type value false .default
  withReader (fun ctx => {ctx with lctx := ltx, localInstances := initI}) do
    match (← Lean.Meta.isClassQuick? type) with
    | .none   => return ⟨fv,ltx,initI⟩
    | .some c => return ⟨fv,ltx, (initI.push {className := c, fvar := .fvar fv})⟩
    | .undef  =>
        match (← Lean.Meta.isClassExpensive? type) with
        | .none  => return ⟨fv,ltx,initI⟩
        | .some c => return ⟨fv,ltx, (initI.push {className := c, fvar := .fvar fv})⟩



-- # Load delcarations

inductive LDeclType where
| cd (name : Name) (type: Expr)
| ld (name : Name) (type : Expr) (value : Expr)
deriving BEq, Repr, Inhabited

@[inline]
partial def loadLDeclsA (data : Array LDeclType) (initD : LocalContext) (initI : LocalInstances) : MetaM (LocalContext × LocalInstances) := do
  let rec go (i : Nat) (initD : LocalContext) (initI : LocalInstances) : MetaM (LocalContext × LocalInstances) := do
    if h : i < data.size
    then
      match data[i] with
      | .cd n t =>
          let ⟨_,initD,initI⟩ ← WithLocalDecl n t initD initI
          go (i+1) initD initI
      | .ld n t v =>
          let ⟨_,initD,initI⟩ ← WithLetDecl n t v initD initI
          go (i+1) initD initI
    else
      return ⟨initD,initI⟩
  go 0 initD initI

@[inline]
partial def loadLDeclsL (data : List LDeclType) (initD : LocalContext) (initI : LocalInstances) : MetaM (LocalContext × LocalInstances) := do
  let rec go (data : List LDeclType) (initD : LocalContext) (initI : LocalInstances) : MetaM (LocalContext × LocalInstances) := do
    match data with
    | [] => return ⟨initD,initI⟩
    | e :: es =>
        match e with
        | .cd n t =>
            let ⟨_,initD,initI⟩ ← WithLocalDecl n t initD initI
            go es initD initI
        | .ld n t v =>
            let ⟨_,initD,initI⟩ ← WithLetDecl n t v initD initI
            go es initD initI
  go data initD initI



-- # Free


@[inline]
def withFreeingNonInst (n : Name) (type body: Expr) (init : LocalContext) : Prod3 FVarId Expr LocalContext :=
  let (fv, init) := withNonInstLocalDecl n type init
  let body := Expr.instantiate1 body (.fvar fv)
  ⟨fv,body,init⟩

@[inline]
def withFreeingLetNonInst (n : Name) (type value body: Expr) (init : LocalContext) : Prod3 FVarId Expr LocalContext :=
  let (fv, init) := withNonInstLetDecl n type value init
  let body := Expr.instantiate1 body (.fvar fv)
  ⟨fv,body,init⟩

@[inline]
def withFreeing (n : Name) (type body: Expr) (initD : LocalContext) (initI : LocalInstances)
  : MetaM (Prod4 FVarId Expr LocalContext LocalInstances) := do
  let ⟨fv, initD, initL⟩ ← WithLocalDecl n type initD initI
  let body := Expr.instantiate1 body (.fvar fv)
  return ⟨fv,body,initD,initL⟩


@[inline]
def withFreeingLet (n : Name) (type value body: Expr) (initD : LocalContext) (initI : LocalInstances)
  : MetaM (Prod4 FVarId Expr LocalContext LocalInstances) := do
  let ⟨fv, initD, initL⟩ ← WithLetDecl n type value initD initI
  let body := Expr.instantiate1 body (.fvar fv)
  return ⟨fv,body,initD,initL⟩



/-- Based on `lambdaTelescopeImp -/
@[inline]
def LambdaLetTelescope (e : Expr) (initD : LocalContext) (initI : LocalInstances)
    : MetaM (Prod4 Expr (Array Expr) LocalContext LocalInstances) := do
  process initD initI #[] e
where
  process (initD : LocalContext) (initI : LocalInstances) (fvars : Array Expr) (e : Expr)
    : MetaM (Prod4 Expr (Array Expr) LocalContext LocalInstances) := do
      match e with
      | .lam n d b bi =>
          let d := d.instantiateRevRange 0 fvars.size fvars
          let d := d.cleanupAnnotations
          match bi with
          | .instImplicit =>
              let ⟨fvarId, initD,initI⟩ ← WithLocalDeclU n d initD initI
              let fvar := mkFVar fvarId
              process initD initI (fvars.push fvar) b
          | _ =>
              let (fvarId, initD) ← withNonInstLocalDeclU n d initD
              let fvar := mkFVar fvarId
              process initD initI (fvars.push fvar) b
      | .letE n t v b _ =>
          let t := t.instantiateRevRange 0 fvars.size fvars
          let t := t.cleanupAnnotations
          let v := v.instantiateRevRange 0 fvars.size fvars
          let ⟨fvarId, initD,initI⟩ ← WithLetDeclU n t v initD initI
          let fvar := mkFVar fvarId
          process initD initI (fvars.push fvar) b
      | _ =>
          let e := e.instantiateRevRange 0 fvars.size fvars
          return ⟨e, fvars, initD, initI⟩

@[inline]
def LambdaLetBoundedTelescope (e : Expr) (initD : LocalContext) (initI : LocalInstances) (maxFVars : Nat)
    : MetaM (Prod4 Expr (Array Expr) LocalContext LocalInstances) := do
  process initD initI #[] e
where
  process (initD : LocalContext) (initI : LocalInstances) (fvars : Array Expr) (e : Expr)
    : MetaM (Prod4 Expr (Array Expr) LocalContext LocalInstances) := do
    if (Nat.blt fvars.size maxFVars)
    then
      match e with
      | .lam n d b bi =>
          let d := d.instantiateRevRange 0 fvars.size fvars
          let d := d.cleanupAnnotations
          match bi with
          | .instImplicit =>
              let ⟨fvarId, initD,initI⟩ ← WithLocalDeclU n d initD initI
              let fvar := mkFVar fvarId
              process initD initI (fvars.push fvar) b
          | _ =>
              let (fvarId, initD) ← withNonInstLocalDeclU n d initD
              let fvar := mkFVar fvarId
              process initD initI (fvars.push fvar) b
      | .letE n t v b _ =>
          let t := t.instantiateRevRange 0 fvars.size fvars
          let t := t.cleanupAnnotations
          let v := v.instantiateRevRange 0 fvars.size fvars
          let ⟨fvarId, initD,initI⟩ ← WithLetDeclU n t v initD initI
          let fvar := mkFVar fvarId
          process initD initI (fvars.push fvar) b
      | _ =>
          let e := e.instantiateRevRange 0 fvars.size fvars
          return ⟨e, fvars, initD, initI⟩
    else
      let e := e.instantiateRevRange 0 fvars.size fvars
      return ⟨e, fvars, initD, initI⟩


@[inline]
def ForallLetTelescope (e : Expr) (initD : LocalContext) (initI : LocalInstances)
    : MetaM (Prod4 Expr (Array Expr) LocalContext LocalInstances) := do
  process initD initI #[] e
where
  process (initD : LocalContext) (initI : LocalInstances) (fvars : Array Expr) (e : Expr)
    : MetaM (Prod4 Expr (Array Expr) LocalContext LocalInstances) := do
      match e with
      | .forallE n d b bi =>
          let d := d.instantiateRevRange 0 fvars.size fvars
          let d := d.cleanupAnnotations
          match bi with
          | .instImplicit =>
              let ⟨fvarId, initD,initI⟩ ← WithLocalDeclU n d initD initI
              let fvar := mkFVar fvarId
              process initD initI (fvars.push fvar) b
          | _ =>
              let (fvarId, initD) ← withNonInstLocalDeclU n d initD
              let fvar := mkFVar fvarId
              process initD initI (fvars.push fvar) b
      | .letE n t v b _ =>
          let t := t.instantiateRevRange 0 fvars.size fvars
          let t := t.cleanupAnnotations
          let v := v.instantiateRevRange 0 fvars.size fvars
          let ⟨fvarId, initD,initI⟩ ← WithLetDeclU n t v initD initI
          let fvar := mkFVar fvarId
          process initD initI (fvars.push fvar) b
      | _ =>
          let e := e.instantiateRevRange 0 fvars.size fvars
          return ⟨e, fvars, initD, initI⟩

@[inline]
def ForallLetBoundedTelescope (e : Expr) (initD : LocalContext) (initI : LocalInstances) (maxFVars : Nat)
    : MetaM (Prod4 Expr (Array Expr) LocalContext LocalInstances) := do
  process initD initI #[] e
where
  process (initD : LocalContext) (initI : LocalInstances) (fvars : Array Expr) (e : Expr)
    : MetaM (Prod4 Expr (Array Expr) LocalContext LocalInstances) := do
    if (Nat.blt fvars.size maxFVars)
    then
      match e with
      | .forallE n d b bi =>
          let d := d.instantiateRevRange 0 fvars.size fvars
          let d := d.cleanupAnnotations
          match bi with
          | .instImplicit =>
              let ⟨fvarId, initD,initI⟩ ← WithLocalDeclU n d initD initI
              let fvar := mkFVar fvarId
              process initD initI (fvars.push fvar) b
          | _ =>
              let (fvarId, initD) ← withNonInstLocalDeclU n d initD
              let fvar := mkFVar fvarId
              process initD initI (fvars.push fvar) b
      | .letE n t v b _ =>
          let t := t.instantiateRevRange 0 fvars.size fvars
          let t := t.cleanupAnnotations
          let v := v.instantiateRevRange 0 fvars.size fvars
          let ⟨fvarId, initD,initI⟩ ← WithLetDeclU n t v initD initI
          let fvar := mkFVar fvarId
          process initD initI (fvars.push fvar) b
      | _ =>
          let e := e.instantiateRevRange 0 fvars.size fvars
          return ⟨e, fvars, initD, initI⟩
    else
      let e := e.instantiateRevRange 0 fvars.size fvars
      return ⟨e, fvars, initD, initI⟩



/-- Based on `lambdaTelescopeImp -/
@[inline]
def LambdaLetTelescopeWW (e : Expr) (initDepth : Nat) (initD : LocalContext) (initI : LocalInstances)
    : MetaM (Prod4 Expr (Array Expr) LocalContext LocalInstances) := do
  process initDepth initD initI #[] e
where
  process (D : Nat) (initD : LocalContext) (initI : LocalInstances) (fvars : Array Expr) (e : Expr)
    : MetaM (Prod4 Expr (Array Expr) LocalContext LocalInstances) := do
      match e with
      | .lam _ d b bi =>
          let n ← worker D
          let d := d.instantiateRevRange 0 fvars.size fvars
          let d := d.cleanupAnnotations
          match bi with
          | .instImplicit =>
              let ⟨fvarId, initD,initI⟩ ← WithLocalDeclU n d initD initI
              let fvar := mkFVar fvarId
              process (D+1) initD initI (fvars.push fvar) b
          | _ =>
              let (fvarId, initD) ← withNonInstLocalDeclU n d initD
              let fvar := mkFVar fvarId
              process (D+1) initD initI (fvars.push fvar) b
      | .letE _ t v b _ =>
          let n ← worker D
          let t := t.instantiateRevRange 0 fvars.size fvars
          let t := t.cleanupAnnotations
          let v := v.instantiateRevRange 0 fvars.size fvars
          let ⟨fvarId, initD,initI⟩ ← WithLetDeclU n t v initD initI
          let fvar := mkFVar fvarId
          process (D+1) initD initI (fvars.push fvar) b
      | _ =>
          let e := e.instantiateRevRange 0 fvars.size fvars
          return ⟨e, fvars, initD, initI⟩


@[inline]
def LambdaLetBoundedTelescopeWW (e : Expr) (initDepth : Nat) (initD : LocalContext) (initI : LocalInstances) (maxFVars : Nat)
    : MetaM (Prod4 Expr (Array Expr) LocalContext LocalInstances) := do
  process initDepth initD initI #[] e
where
  process (D : Nat) (initD : LocalContext) (initI : LocalInstances) (fvars : Array Expr) (e : Expr)
    : MetaM (Prod4 Expr (Array Expr) LocalContext LocalInstances) := do
    if (Nat.blt fvars.size maxFVars)
    then
      match e with
      | .lam _ d b bi =>
          let n ← worker D
          let d := d.instantiateRevRange 0 fvars.size fvars
          let d := d.cleanupAnnotations
          match bi with
          | .instImplicit =>
              let ⟨fvarId, initD,initI⟩ ← WithLocalDeclU n d initD initI
              let fvar := mkFVar fvarId
              process (D+1) initD initI (fvars.push fvar) b
          | _ =>
              let (fvarId, initD) ← withNonInstLocalDeclU n d initD
              let fvar := mkFVar fvarId
              process (D+1) initD initI (fvars.push fvar) b
      | .letE _ t v b _ =>
          let n ← worker D
          let t := t.instantiateRevRange 0 fvars.size fvars
          let t := t.cleanupAnnotations
          let v := v.instantiateRevRange 0 fvars.size fvars
          let ⟨fvarId, initD,initI⟩ ← WithLetDeclU n t v initD initI
          let fvar := mkFVar fvarId
          process (D+1) initD initI (fvars.push fvar) b
      | _ =>
          let e := e.instantiateRevRange 0 fvars.size fvars
          return ⟨e, fvars, initD, initI⟩
    else
      let e := e.instantiateRevRange 0 fvars.size fvars
      return ⟨e, fvars, initD, initI⟩


@[inline]
def ForallLetTelescopeWW (e : Expr) (initDepth : Nat) (initD : LocalContext) (initI : LocalInstances)
    : MetaM (Prod4 Expr (Array Expr) LocalContext LocalInstances) := do
  process initDepth initD initI #[] e
where
  process (D : Nat) (initD : LocalContext) (initI : LocalInstances) (fvars : Array Expr) (e : Expr)
    : MetaM (Prod4 Expr (Array Expr) LocalContext LocalInstances) := do
      match e with
      | .forallE _ d b bi =>
          let n ← worker D
          let d := d.instantiateRevRange 0 fvars.size fvars
          let d := d.cleanupAnnotations
          match bi with
          | .instImplicit =>
              let ⟨fvarId, initD,initI⟩ ← WithLocalDeclU n d initD initI
              let fvar := mkFVar fvarId
              process (D+1) initD initI (fvars.push fvar) b
          | _ =>
              let (fvarId, initD) ← withNonInstLocalDeclU n d initD
              let fvar := mkFVar fvarId
              process (D+1) initD initI (fvars.push fvar) b
      | .letE _ t v b _ =>
          let n ← worker D
          let t := t.instantiateRevRange 0 fvars.size fvars
          let t := t.cleanupAnnotations
          let v := v.instantiateRevRange 0 fvars.size fvars
          let ⟨fvarId, initD,initI⟩ ← WithLetDeclU n t v initD initI
          let fvar := mkFVar fvarId
          process (D+1) initD initI (fvars.push fvar) b
      | _ =>
          let e := e.instantiateRevRange 0 fvars.size fvars
          return ⟨e, fvars, initD, initI⟩

@[inline]
def ForallLetBoundedTelescopeWW (e : Expr) (initDepth : Nat) (initD : LocalContext) (initI : LocalInstances) (maxFVars : Nat)
    : MetaM (Prod4 Expr (Array Expr) LocalContext LocalInstances) := do
  process initDepth initD initI #[] e
where
  process (D : Nat) (initD : LocalContext) (initI : LocalInstances) (fvars : Array Expr) (e : Expr)
    : MetaM (Prod4 Expr (Array Expr) LocalContext LocalInstances) := do
    if (Nat.blt fvars.size maxFVars)
    then
      match e with
      | .forallE _ d b bi =>
          let n ← worker D
          let d := d.instantiateRevRange 0 fvars.size fvars
          let d := d.cleanupAnnotations
          match bi with
          | .instImplicit =>
              let ⟨fvarId, initD,initI⟩ ← WithLocalDeclU n d initD initI
              let fvar := mkFVar fvarId
              process (D+1) initD initI (fvars.push fvar) b
          | _ =>
              let (fvarId, initD) ← withNonInstLocalDeclU n d initD
              let fvar := mkFVar fvarId
              process (D+1) initD initI (fvars.push fvar) b
      | .letE _ t v b _ =>
          let n ← worker D
          let t := t.instantiateRevRange 0 fvars.size fvars
          let t := t.cleanupAnnotations
          let v := v.instantiateRevRange 0 fvars.size fvars
          let ⟨fvarId, initD,initI⟩ ← WithLetDeclU n t v initD initI
          let fvar := mkFVar fvarId
          process (D+1) initD initI (fvars.push fvar) b
      | _ =>
          let e := e.instantiateRevRange 0 fvars.size fvars
          return ⟨e, fvars, initD, initI⟩
    else
      let e := e.instantiateRevRange 0 fvars.size fvars
      return ⟨e, fvars, initD, initI⟩





-- # Printing


def printMetaMContextDecls_1 : MetaM String := do
  let ctx ← read
  let mut decls : List String := ["Local decls (hashmap, pp):"]
  for (fvid,dec) in ctx.lctx.fvarIdToDecl do
    decls := s!"▸ {repr fvid} : {← ppExpr dec.type}" :: decls
  decls := "Local instances:" :: decls
  for dec in ctx.localInstances do
    decls := s!"▸ {← ppExpr dec.fvar} : {dec.className}" :: decls
  return String.intercalate "\n" decls


def printMetaMContextDecls_2 : MetaM String := do
  let ctx ← read
  let mut decls : List String := ["Local decls (hashmap, not pp):"]
  for (fvid,dec) in ctx.lctx.fvarIdToDecl do
    decls := s!"▸ {repr fvid} : {dec.type}" :: decls
  decls := "Local instances:" :: decls
  for dec in ctx.localInstances do
    decls := s!"▸ {← ppExpr dec.fvar} : {dec.className}" :: decls
  return String.intercalate "\n" decls


def printMetaMContextDecls_3 : MetaM String := do
  let ctx ← read
  let mut decls : List String := ["Local decls (parray, pp):"]
  for dec? in ctx.lctx.decls do
    let .some dec := dec? | continue
    decls := s!"▸ {repr dec.fvarId} : {← ppExpr dec.type}" :: decls
  decls := "Local instances:" :: decls
  for dec in ctx.localInstances do
    decls := s!"▸ {← ppExpr dec.fvar} : {dec.className}" :: decls
  return String.intercalate "\n" decls

def printMetaMContextDecls_4 : MetaM String := do
  let ctx ← read
  let mut decls : List String := ["Local decls (parray, not pp):"]
  for dec? in ctx.lctx.decls do
    let .some dec := dec? | continue
    decls := s!"▸ {repr dec.fvarId} : {dec.type}" :: decls
  decls := "Local instances:" :: decls
  for dec in ctx.localInstances do
    decls := s!"▸ {← ppExpr dec.fvar} : {dec.className}" :: decls
  return String.intercalate "\n" decls
