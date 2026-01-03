
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Utils.Tracing
import LeanGrow.Src.Utils.Lean.LocalContext
import LeanGrow.Src.Utils.Lean.Expr.Fail
import LeanGrow.Src.Utils.LeanGrow.Nodes

open Lean Meta



private inductive AssembleTask where
| nil
| app (_ : AssembleTask) (post? : Bool)
| lam (_ : Name) (_ : BinderInfo) (_ : AssembleTask) (post? : Bool)
| all (_ : Name) (_ : BinderInfo) (_ : AssembleTask) (post? : Bool)
| letE (_ : Name) (_ : Bool) (_ : AssembleTask) (postNum : UInt8)
| proj (_ : Name) (_ : Nat) (_ : AssembleTask)
| mdata (_ : MData) (_ : AssembleTask)
deriving Inhabited, Repr, BEq


mutual
@[specialize f]
private partial def goUp_1 (f : Expr → Expr) (ta : List Expr) (aT : AssembleTask) : List Expr → Expr
  | last@([]) =>
    trace set TracingFlags.none in
    trace on .zero with s!"[onAllSubterms] empty todos ; \n  ta : {repr ta}\n  aT : {repr aT}" in
    match aT with
    | .proj n i ats =>
      match ta with
      | x :: L => goUp_1 f ((.proj n i x) :: L) ats last
      | _ => failExpr "onAllSubterms"
    | .mdata d ats =>
      match ta with
      | x :: L => goUp_1 f ((.mdata d x) :: L) ats last
      | _ => failExpr "onAllSubterms"
    | .app ats false =>
      match ta with
      | x :: y :: L => goUp_1 f ((.app y x) :: L) ats last
      | _ => failExpr "onAllSubterms"
    | .lam n i ats false =>
      match ta with
      | x :: y :: L => goUp_1 f ((.lam n y x i) :: L) ats last
      | _ => failExpr "onAllSubterms"
    | .all n i ats false =>
      match ta with
      | x :: y :: L => goUp_1 f ((.forallE n y x i) :: L) ats last
      | _ => failExpr "onAllSubterms"
    | .letE n i ats _ =>
      match ta with
      | x :: y :: z :: L => goUp_1 f ((.letE n z y x i) :: L) ats last
      | _ => failExpr "onAllSubterms"
    | .nil =>
      match ta with
      | res :: _ => res
      | _ => failExpr "onAllSubterms"
    | _ => failExpr "onAllSubterms"
  | todo@(_ :: _) =>
    trace set TracingFlags.none in
    trace on .zero with s!"[onAllSubterms]\n  ta : {repr ta}\n  aT : {repr aT}\n  todo : {repr todo}" in
    match aT with
    | .proj n i ats =>
      match ta with
      | x :: L => goUp_1 f ((.proj n i x) :: L) ats todo
      | _ => failExpr "onAllSubterms"
    | .mdata d ats =>
      match ta with
      | x :: L => goUp_1 f ((.mdata d x) :: L) ats todo
      | _ => failExpr "onAllSubterms"
    | .app ats true => goDown_1 f ta (.app ats false) todo
    | .app ats false =>
      match ta with
      | x :: y :: L => goUp_1 f  ((.app y x) :: L) ats todo
      | _ => failExpr "onAllSubterms"
    | .lam n i ats true => goDown_1 f ta (.lam n i ats false) todo
    | .lam n i ats false =>
      match ta with
      | x :: y :: L => goUp_1 f  ((.lam n y x i) :: L) ats todo
      | _ => failExpr "onAllSubterms"
    | .all n i ats true => goDown_1 f ta (.all n i ats false) todo
    | .all n i ats false =>
      match ta with
      | x :: y :: L => goUp_1 f  ((.forallE n y x i) :: L) ats todo
      | _ => failExpr "onAllSubterms"
    | .letE n i ats pn =>
      if pn == 0
      then
        match ta with
        | x :: y :: z :: L => goUp_1 f  ((.letE n z y x i) :: L) ats todo
        | _ => failExpr "onAllSubterms"
      else
        goDown_1 f ta (.letE n i ats (pn-1)) todo
    | _ => failExpr "onAllSubterms"

@[specialize f]
private partial def goDown_1 (f : Expr → Expr) (ta : List Expr) (aT : AssembleTask) (todo : List Expr) : Expr :=
  trace set TracingFlags.none in
  match todo with
  | (nx :: more) =>
    let here := f nx
    trace on .zero with s!"[onAllSubterms]\n  here : {repr here}\n  ta : {repr ta}\n  aT : {repr aT}\n  todo : {repr todo}" in
    match here with
    | .const _ _ | .lit _ | .mvar _ | .fvar _ | .bvar _  | .sort _ =>
        goUp_1 f (here :: ta) aT more
    | .app l r => goDown_1 f ta (.app aT true) (l :: r :: more)
    | .lam n l r i => goDown_1 f ta (.lam n i aT true) (l :: r :: more)
    | .forallE n l r i => goDown_1 f ta (.all n i aT true) (l :: r :: more)
    | .letE n l r z i => goDown_1 f ta (.letE n i aT 2) (l :: r :: z :: more)
    | .proj n i l => goDown_1 f ta (.proj n i aT) (l :: more)
    | .mdata d l => goDown_1 f ta (.mdata d aT) (l :: more)
  | _ => failExpr "onAllSubterms"
end

@[specialize f, inline]
def Lean.Expr.onAllSubtermsTR (e : Expr) (f : Expr → Expr) : Expr :=
  goDown_1 f [] .nil [e]



@[specialize f, inline]
partial def Lean.Expr.onAllSubterms (e : Expr) (f : Expr → Expr) : Expr :=
  let rec @[specialize f] go (e : Expr) (C : ExprMap Expr) : Expr × ExprMap Expr :=
    match C[e]? with
    | .some res => (res,C)
    | _ =>
      match f e with
      | .app l r =>
        let (l,C) := go l C
        let (r,C) := go r C
        let R := .app l r
        let C := C.insert e R
        (R, C)
      | .lam n l r bi =>
        let (l,C) := go l C
        let (r,C) := go r C
        let R := .lam n l r bi
        let C := C.insert e R
        (R, C)
      | .forallE n l r bi =>
        let (l,C) := go l C
        let (r,C) := go r C
        let R := .forallE n l r bi
        let C := C.insert e R
        (R, C)
      | .letE n l r z bi =>
        let (l,C) := go l C
        let (r,C) := go r C
        let (z,C) := go z C
        let R := .letE n l r z bi
        let C := C.insert e R
        (R, C)
      | .proj n i l =>
        let (l,C) := go l C
        let R := .proj n i l
        let C := C.insert e R
        (R, C)
      | .mdata d l =>
        let (l,C) := go l C
        let R := .mdata d l
        let C := C.insert e R
        (R, C)
      | t => (t,C.insert e t)
  (go e {}).1




@[specialize f, inline]
partial def Lean.Expr.onAllSubtermsWiDepthTR (e : Expr) (f : Expr → Nat → Expr) : Expr :=
  trace set TracingFlags.none in
  let rec @[specialize f] go (ta : List Expr) (aT : AssembleTask) (up? : Bool) : ListProd Nat Expr → Expr
    | last@(.nil) =>
      trace on .zero with s!"[onAllSubterms] empty todos ; \n  ta : {repr ta}\n  aT : {repr aT}" in
      match aT with
      | .proj n i ats =>
        match ta with
        | x :: L => go ((.proj n i x) :: L) ats up? last
        | _ => failExpr "onAllSubterms"
      | .mdata d ats =>
        match ta with
        | x :: L => go ((.mdata d x) :: L) ats up? last
        | _ => failExpr "onAllSubterms"
      | .app ats false =>
        match ta with
        | x :: y :: L => go ((.app y x) :: L) ats up? last
        | _ => failExpr "onAllSubterms"
      | .lam n i ats false =>
        match ta with
        | x :: y :: L => go ((.lam n y x i) :: L) ats up? last
        | _ => failExpr "onAllSubterms"
      | .all n i ats false =>
        match ta with
        | x :: y :: L => go ((.forallE n y x i) :: L) ats up? last
        | _ => failExpr "onAllSubterms"
      | .letE n i ats _ =>
        match ta with
        | x :: y :: z :: L => go ((.letE n z y x i) :: L) ats up? last
        | _ => failExpr "onAllSubterms"
      | .nil =>
        match ta with
        | res :: _ => res
        | _ => failExpr "onAllSubterms"
      | _ => failExpr "onAllSubterms"
    | todo@(.cons depth nx more) =>
      trace on .zero with s!"[onAllSubterms] cons todos ; mode up? is {up?}" in
      if up?
      then
        trace on .zero with s!"[onAllSubterms]\n  ta : {repr ta}\n  aT : {repr aT}\n  todo : {repr todo}" in
        match aT with
        | .proj n i ats =>
          match ta with
          | x :: L => go ((.proj n i x) :: L) ats up? todo
          | _ => failExpr "onAllSubterms"
        | .mdata d ats =>
          match ta with
          | x :: L => go ((.mdata d x) :: L) ats up? todo
          | _ => failExpr "onAllSubterms"
        | .app ats true => go ta (.app ats false) false todo
        | .app ats false =>
          match ta with
          | x :: y :: L => go ((.app y x) :: L) ats up? todo
          | _ => failExpr "onAllSubterms"
        | .lam n i ats true => go ta (.lam n i ats false) false todo
        | .lam n i ats false =>
          match ta with
          | x :: y :: L => go ((.lam n y x i) :: L) ats up? todo
          | _ => failExpr "onAllSubterms"
        | .all n i ats true => go ta (.all n i ats false) false todo
        | .all n i ats false =>
          match ta with
          | x :: y :: L => go ((.forallE n y x i) :: L) ats up? todo
          | _ => failExpr "onAllSubterms"
        | .letE n i ats pn =>
          if pn == 0
          then
            match ta with
            | x :: y :: z :: L => go ((.letE n z y x i) :: L) ats up? todo
            | _ => failExpr "onAllSubterms"
          else
            go ta (.letE n i ats (pn-1)) false todo
        | _ => failExpr "onAllSubterms"
      else
        let here := f nx depth
        trace on .zero with s!"[onAllSubterms]\n  here : {repr here}\n  ta : {repr ta}\n  aT : {repr aT}\n  todo : {repr todo}" in
        match here with
        | .const _ _ | .lit _ | .mvar _ | .fvar _ | .bvar _  | .sort _ =>
            go (here :: ta) aT true more
        | .app l r => go ta (.app aT true) false (.cons depth l <| .cons depth r more)
        | .lam n l r i => go ta (.lam n i aT true) false (.cons depth l <| .cons (depth + 1) r more)
        | .forallE n l r i => go ta (.all n i aT true) false (.cons depth l <| .cons (depth + 1) r more)
        | .letE n l r z i => go ta (.letE n i aT 2) false (.cons depth l <| .cons depth r <| .cons (depth + 1) z more)
        | .proj n i l => go ta (.proj n i aT) false (.cons depth l more)
        | .mdata d l => go ta (.mdata d aT) false (.cons depth l more)
  go [] .nil false <| .cons 0 e .nil


@[specialize f, inline]
partial def Lean.Expr.onAllSubtermsWiDepth (e : Expr) (f : Expr → Nat → Expr) : Expr :=
  let rec @[specialize f] go (e : Expr) (d : Nat) (C : ExprMap Expr) : Expr × ExprMap Expr :=
    match C[e]? with
    | .some res => (res,C)
    | _ =>
      match f e d with
      | .app l r =>
        let (l,C) := go l d C
        let (r,C) := go r d C
        let R := .app l r
        let C := C.insert e R
        (R, C)
      | .lam n l r bi =>
        let (l,C) := go l d C
        let (r,C) := go r (d+1) C
        let R := .lam n l r bi
        let C := C.insert e R
        (R, C)
      | .forallE n l r bi =>
        let (l,C) := go l d C
        let (r,C) := go r (d+1) C
        let R := .forallE n l r bi
        let C := C.insert e R
        (R, C)
      | .letE n l r z bi =>
        let (l,C) := go l d C
        let (r,C) := go r d C
        let (z,C) := go z (d+1) C
        let R := .letE n l r z bi
        let C := C.insert e R
        (R, C)
      | .proj n i l =>
        let (l,C) := go l d C
        let R := .proj n i l
        let C := C.insert e R
        (R, C)
      | .mdata da l =>
        let (l,C) := go l d C
        let R := .mdata da l
        let C := C.insert e R
        (R, C)
      | t => (t,C.insert e t)
  (go e 0 {}).1




private inductive AssembleTaskMeta where
| nil
| app (_ : AssembleTaskMeta) (post? : Bool)
| lam (_ : Name) (_ : BinderInfo) (_ : Expr) (binfo : Nat) (_ : AssembleTaskMeta) (post? : Bool)
| all (_ : Name) (_ : BinderInfo) (_ : Expr) (binfo : Nat) (_ : AssembleTaskMeta) (post? : Bool)
| letE (_ : Name) (_ : Bool) (_ : Expr) (binfo : Nat) (_ : AssembleTaskMeta) (postNum : UInt8)
| proj (_ : Name) (_ : Nat) (_ : AssembleTaskMeta)
| mdata (_ : MData) (_ : AssembleTaskMeta)
deriving Inhabited, Repr, BEq

/--
For `f`, we conserder bvar i loose if i ≥ d
-/
@[specialize f,inline]
partial def Lean.Expr.onAllSubtermsMTR (e : Expr) (initD : LocalContext) (initI : LocalInstances)
  (f : Expr → Nat → LocalContext → LocalInstances → MetaM (Prod3 Expr LocalContext LocalInstances)) : MetaM (Prod3 Expr LocalContext LocalInstances) :=
  trace set TracingFlags.none in
  let rec @[specialize f] go (initD : LocalContext) (initI : LocalInstances) (ta : List Expr) (aT : AssembleTaskMeta) (up? : Bool)
  : ListProd Nat Expr → MetaM (Prod3 Expr LocalContext LocalInstances)
    | last@(.nil) => do
      trace on .zero with s!"[onAllSubterms] empty todos ; \n  ta : {repr ta}\n  aT : {repr aT}" in
      match aT with
      | .proj n i ats =>
        match ta with
        | x :: L => go initD initI ((.proj n i x) :: L) ats up? last
        | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
      | .mdata d ats =>
        match ta with
        | x :: L => go initD initI ((.mdata d x) :: L) ats up? last
        | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
      | .app ats false =>
        match ta with
        | x :: y :: L => go initD initI ((.app y x) :: L) ats up? last
        | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
      | .lam n i fv binfo ats false =>
        match ta with
        | x :: y :: L => do
          let X := x.abstract #[ fv]
          let initI := initI.patch binfo 1
          go initD initI ((.lam n y X i) :: L) ats up? last
        | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
      | .all n i fv binfo ats false =>
        match ta with
        | x :: y :: L =>  do
          let X := x.abstract #[ fv]
          let initI := initI.patch binfo 1
          go initD initI ((.forallE n y X i) :: L) ats up? last
        | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
      | .letE n i fv binfo ats _ =>
        match ta with
        | x :: y :: z :: L => do
          let X := x.abstract #[ fv]
          let initI := initI.patch binfo 1
          go initD initI ((.letE n z y X i) :: L) ats up? last
        | _ =>
          let initI := initI.patch binfo 1
          return ⟨failExpr "onAllSubterms",initD,initI⟩
      | .nil =>
        match ta with
        | res :: _ => return ⟨res,initD,initI⟩
        | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
      | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
    | todo@(.cons depth nx more) => do
      trace on .zero with s!"[onAllSubterms] cons todos ; mode up? is {up?}" in
      if up?
      then
        trace on .zero with s!"[onAllSubterms]\n  ta : {repr ta}\n  aT : {repr aT}\n  todo : {repr todo}" in
        match aT with
        | .proj n i ats =>
          match ta with
          | x :: L => go initD initI ((.proj n i x) :: L) ats up? todo
          | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
        | .mdata d ats =>
          match ta with
          | x :: L => go initD initI ((.mdata d x) :: L) ats up? todo
          | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
        | .app ats true => go initD initI ta (.app ats false) false todo
        | .app ats false =>
          match ta with
          | x :: y :: L => go initD initI ((.app y x) :: L) ats up? todo
          | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
        | .lam n i fv binfo ats true => go initD initI ta (.lam n i fv binfo ats false) false todo
        | .lam n i fv binfo ats false =>
          match ta with
          | x :: y :: L => do
          let X := x.abstract #[ fv]
          let initI := initI.patch binfo 1
          go initD initI ((.lam n y X i) :: L) ats up? todo
          | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
        | .all n i fv binfo ats true => go initD initI ta (.all n i fv binfo ats false) false todo
        | .all n i fv binfo ats false =>
          match ta with
          | x :: y :: L => do
          let X := x.abstract #[ fv]
          let initI := initI.patch binfo 1
          go initD initI ((.forallE n y X i) :: L) ats up? todo
          | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
        | .letE n i fv binfo ats pn =>
          if pn == 0
          then
            match ta with
            | x :: y :: z :: L => do
              let X := x.abstract #[ fv]
              let initI := initI.patch binfo 1
              go initD initI ((.letE n z y X i) :: L) ats up? todo
            | _ =>
              let initI := initI.patch binfo 1
              return ⟨failExpr "onAllSubterms",initD,initI⟩
          else
            go initD initI ta (.letE n i fv binfo ats (pn-1)) false todo
        | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
      else do
        let here ← f nx depth initD initI
        trace on .zero with s!"[onAllSubterms]\n  here : {repr here}\n  ta : {repr ta}\n  aT : {repr aT}\n  todo : {repr todo}" in
        let initD := here.2
        let initI := here.3
        let here := here.1
        match here with
        | .const _ _ | .lit _ | .mvar _ | .fvar _ | .bvar _  | .sort _ =>
            go initD initI (here :: ta) aT true more
        | .app l r => go initD initI ta (.app aT true) false (.cons depth l <| .cons depth r more)
        | .lam n l r i => do
          let S := initI.size
          let fv ←  worker depth
          let ⟨fv,r,initD,initI⟩ ← withFreeing fv l r initD initI
          -- BUG POTENTIAL : may introduce a local instance that will be present durring manipulation of its own type
          go initD initI ta (.lam n i (.fvar fv) S aT true) false (.cons depth l <| .cons (depth + 1) r more)
        | .forallE n l r i => do
          let S := initI.size
          let fv ←  worker depth
          let ⟨fv,r,initD,initI⟩ ← withFreeing fv l r initD initI
          go initD initI ta (.all n i (.fvar fv) S aT true) false (.cons depth l <| .cons (depth + 1) r more)
        | .letE n l r z i => do
          let S := initI.size
          let fv ←  worker depth
          let ⟨fv,z,initD,initI⟩ ← withFreeingLet fv l r z initD initI
          go initD initI ta (.letE n i (.fvar fv) S aT 2) false (.cons depth l <| .cons depth r <| .cons (depth + 1) z more)
        | .proj n i l => go initD initI ta (.proj n i aT) false (.cons depth l more)
        | .mdata d l => go initD initI ta (.mdata d aT) false (.cons depth l more)
  go initD initI [] .nil false (.cons 0 e .nil)


@[specialize f, inline]
partial def Lean.Expr.onAllSubtermsM (e : Expr) (l1 : LocalContext) (l2 : LocalInstances)
  (f : Expr → Nat → LocalContext → LocalInstances → MetaM (Prod3 Expr LocalContext LocalInstances))
  : MetaM (Prod3 Expr LocalContext LocalInstances) :=
  let rec @[specialize f] go (e : Expr) (d : Nat) (l1 : LocalContext) (l2 : LocalInstances) (C : ExprMap Expr)
    : MetaM (Prod4 Expr (ExprMap Expr) LocalContext LocalInstances) := do
    match C[e]? with
    | .some res => return ⟨res,C,l1,l2⟩
    | _ =>
      let ⟨R,l1,l2⟩ ← f e d l1 l2
      match R with
      | .app l r =>
        let ⟨l,C,l1,l2⟩ ← go l d l1 l2 C
        let ⟨r,C,l1,l2⟩ ← go r d l1 l2 C
        let R := .app l r
        let C := C.insert e R
        return ⟨R,C,l1,l2⟩
      | .lam n l r bi =>
        let ⟨l,C,l1,l2⟩ ← go l d l1 l2 C
        let S := l2.size
        let fv ←  worker d
        let ⟨_,r,l1,l2⟩ ← withFreeing fv l r l1 l2
        let ⟨r,C,l1,l2⟩ ← go r (d+1) l1 l2 C
        let l2 := match bi with | .instImplicit => l2.patch S 1 | _ => l2
        let R := .lam n l r bi
        let C := C.insert e R
        return ⟨R,C,l1,l2⟩
      | .forallE n l r bi =>
        let ⟨l,C,l1,l2⟩ ← go l d l1 l2 C
        let S := l2.size
        let fv ←  worker d
        let ⟨_,r,l1,l2⟩ ← withFreeing fv l r l1 l2
        let ⟨r,C,l1,l2⟩ ← go r (d+1) l1 l2 C
        let l2 := match bi with | .instImplicit => l2.patch S 1 | _ => l2
        let R := .forallE n l r bi
        let C := C.insert e R
        return ⟨R,C,l1,l2⟩
      | .letE n l r z bi =>
        let ⟨l,C,l1,l2⟩ ← go l d l1 l2 C
        let ⟨r,C,l1,l2⟩ ← go r d l1 l2 C
        let S := l2.size
        let fv ←  worker d
        let ⟨_,z,l1,l2⟩ ← withFreeingLet fv l r z l1 l2
        let ⟨z,C,l1,l2⟩ ← go z (d+1) l1 l2 C
        let l2 := if (← withLCtx l1 l2 (isClass? l)).isSome then l2.patch S 1 else l2
        let R := .letE n l r z bi
        let C := C.insert e R
        return ⟨R,C,l1,l2⟩
      | .proj n i l =>
        let ⟨l,C,l1,l2⟩ ← go l d l1 l2 C
        let R := .proj n i l
        let C := C.insert e R
        return ⟨R,C,l1,l2⟩
      | .mdata da l =>
        let ⟨l,C,l1,l2⟩ ← go l d l1 l2 C
        let R := .mdata da l
        let C := C.insert e R
        return ⟨R,C,l1,l2⟩
      | t => return ⟨t,C.insert e t,l1,l2⟩
  do
  let ⟨r,_,l1,l2⟩ ← go e 0 l1 l2 {}
  return ⟨r,l1,l2⟩



@[specialize f, inline]
partial def Lean.Expr.onAllSubtermsWiWorkerTrackedMTR (e : Expr) (initD : LocalContext) (initI : LocalInstances)
  (f : Expr → Nat → Array Expr → LocalContext → LocalInstances → MetaM (Prod3 Expr LocalContext LocalInstances)) : MetaM (Prod3 Expr LocalContext LocalInstances) :=
  trace set TracingFlags.none in
  let rec @[specialize f] go (workas : Array Expr) (initD : LocalContext) (initI : LocalInstances) (ta : List Expr) (aT : AssembleTaskMeta) (up? : Bool)
  : ListProd Nat Expr → MetaM (Prod3 Expr LocalContext LocalInstances)
    | last@(.nil) => do
      trace on .zero with s!"[onAllSubterms] empty todos ; \n  ta : {repr ta}\n  aT : {repr aT}" in
      match aT with
      | .proj n i ats =>
        match ta with
        | x :: L => go workas initD initI ((.proj n i x) :: L) ats up? last
        | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
      | .mdata d ats =>
        match ta with
        | x :: L => go workas initD initI ((.mdata d x) :: L) ats up? last
        | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
      | .app ats false =>
        match ta with
        | x :: y :: L => go workas initD initI ((.app y x) :: L) ats up? last
        | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
      | .lam n i fv binfo ats false =>
        match ta with
        | x :: y :: L => do
          let X := x.abstract #[ fv]
          let initI := initI.patch binfo 1
          go workas initD initI ((.lam n y X i) :: L) ats up? last
        | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
      | .all n i fv binfo ats false =>
        match ta with
        | x :: y :: L =>  do
          let X := x.abstract #[ fv]
          let initI := initI.patch binfo 1
          go workas initD initI ((.forallE n y X i) :: L) ats up? last
        | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
      | .letE n i fv binfo ats _ =>
        match ta with
        | x :: y :: z :: L => do
          let X := x.abstract #[ fv]
          let initI := initI.patch binfo 1
          go workas initD initI ((.letE n z y X i) :: L) ats up? last
        | _ =>
          let initI := initI.patch binfo 1
          return ⟨failExpr "onAllSubterms",initD,initI⟩
      | .nil =>
        match ta with
        | res :: _ => return ⟨res,initD,initI⟩
        | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
      | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
    | todo@(.cons depth nx more) => do
      trace on .zero with s!"[onAllSubterms] cons todos ; mode up? is {up?}" in
      if up?
      then
        trace on .zero with s!"[onAllSubterms]\n  ta : {repr ta}\n  aT : {repr aT}\n  todo : {repr todo}" in
        match aT with
        | .proj n i ats =>
          match ta with
          | x :: L => go workas initD initI ((.proj n i x) :: L) ats up? todo
          | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
        | .mdata d ats =>
          match ta with
          | x :: L => go workas initD initI ((.mdata d x) :: L) ats up? todo
          | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
        | .app ats true => go workas initD initI ta (.app ats false) false todo
        | .app ats false =>
          match ta with
          | x :: y :: L => go workas initD initI ((.app y x) :: L) ats up? todo
          | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
        | .lam n i fv binfo ats true => go workas initD initI ta (.lam n i fv binfo ats false) false todo
        | .lam n i fv binfo ats false =>
          match ta with
          | x :: y :: L => do
          let X := x.abstract #[ fv]
          let initI := initI.patch binfo 1
          go workas initD initI ((.lam n y X i) :: L) ats up? todo
          | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
        | .all n i fv binfo ats true => go workas initD initI ta (.all n i fv binfo ats false) false todo
        | .all n i fv binfo ats false =>
          match ta with
          | x :: y :: L => do
          let X := x.abstract #[ fv]
          let initI := initI.patch binfo 1
          go workas initD initI ((.forallE n y X i) :: L) ats up? todo
          | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
        | .letE n i fv binfo ats pn =>
          if pn == 0
          then
            match ta with
            | x :: y :: z :: L => do
              let X := x.abstract #[ fv]
              let initI := initI.patch binfo 1
              go workas initD initI ((.letE n z y X i) :: L) ats up? todo
            | _ =>
              let initI := initI.patch binfo 1
              return ⟨failExpr "onAllSubterms",initD,initI⟩
          else
            go workas initD initI ta (.letE n i fv binfo ats (pn-1)) false todo
        | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
      else do
        let here ← f nx depth workas initD initI
        trace on .zero with s!"[onAllSubterms]\n  here : {repr here}\n  ta : {repr ta}\n  aT : {repr aT}\n  todo : {repr todo}" in
        let initD := here.2
        let initI := here.3
        let here := here.1
        match here with
        | .const _ _ | .lit _ | .mvar _ | .fvar _ | .bvar _  | .sort _ =>
            go workas initD initI (here :: ta) aT true more
        | .app l r => go workas initD initI ta (.app aT true) false (.cons depth l <| .cons depth r more)
        | .lam n l r i => do
          let S := initI.size
          let fv ←  worker depth
          let ⟨fv,r,initD,initI⟩ ← withFreeing fv l r initD initI
          -- BUG POTENTIAL : may introduce a local instance that will be present durring manipulation of its own type
          go (workas.push (.fvar fv)) initD initI ta (.lam n i (.fvar fv) S aT true) false (.cons depth l <| .cons (depth + 1) r more)
        | .forallE n l r i => do
          let S := initI.size
          let fv ←  worker depth
          let ⟨fv,r,initD,initI⟩ ← withFreeing fv l r initD initI
          go (workas.push (.fvar fv)) initD initI ta (.all n i (.fvar fv) S aT true) false (.cons depth l <| .cons (depth + 1) r more)
        | .letE n l r z i => do
          let S := initI.size
          let fv ←  worker depth
          let ⟨fv,z,initD,initI⟩ ← withFreeingLet fv l r z initD initI
          go (workas.push (.fvar fv)) initD initI ta (.letE n i (.fvar fv) S aT 2) false (.cons depth l <| .cons depth r <| .cons (depth + 1) z more)
        | .proj n i l => go workas initD initI ta (.proj n i aT) false (.cons depth l more)
        | .mdata d l => go workas initD initI ta (.mdata d aT) false (.cons depth l more)
  go #[] initD initI [] .nil false (.cons 0 e .nil)


@[specialize f, inline]
partial def Lean.Expr.onAllSubtermsWiWorkerTrackedM (e : Expr) (l1 : LocalContext) (l2 : LocalInstances)
  (f : Expr → Nat → Array Expr → LocalContext → LocalInstances → MetaM (Prod3 Expr LocalContext LocalInstances))
  : MetaM (Prod3 Expr LocalContext LocalInstances) :=
  let rec @[specialize f] go (workas : Array Expr) (e : Expr) (d : Nat) (l1 : LocalContext) (l2 : LocalInstances) (C : ExprMap Expr)
    : MetaM (Prod5 Expr (ExprMap Expr) (Array Expr) LocalContext LocalInstances) := do
    match C[e]? with
    | .some res => return ⟨res,C,workas,l1,l2⟩
    | _ =>
      let ⟨R,l1,l2⟩ ← f e d workas l1 l2
      match R with
      | .app l r =>
        let ⟨l,C,workas,l1,l2⟩ ← go workas l d l1 l2 C
        let ⟨r,C,workas,l1,l2⟩ ← go workas r d l1 l2 C
        let R := .app l r
        let C := C.insert e R
        return ⟨R,C,workas,l1,l2⟩
      | .lam n l r bi =>
        let ⟨l,C,workas,l1,l2⟩ ← go workas l d l1 l2 C
        let S := l2.size
        let fv ←  worker d
        let ⟨fv,r,l1,l2⟩ ← withFreeing fv l r l1 l2
        let ⟨r,C,workas,l1,l2⟩ ← go (workas.push (.fvar fv)) r (d+1) l1 l2 C
        let l2 := match bi with | .instImplicit => l2.patch S 1 | _ => l2
        let R := .lam n l r bi
        let C := C.insert e R
        return ⟨R,C,workas,l1,l2⟩
      | .forallE n l r bi =>
        let ⟨l,C,workas,l1,l2⟩ ← go workas l d l1 l2 C
        let S := l2.size
        let fv ←  worker d
        let ⟨fv,r,l1,l2⟩ ← withFreeing fv l r l1 l2
        let ⟨r,C,workas,l1,l2⟩ ← go (workas.push (.fvar fv)) r (d+1) l1 l2 C
        let l2 := match bi with | .instImplicit => l2.patch S 1 | _ => l2
        let R := .forallE n l r bi
        let C := C.insert e R
        return ⟨R,C,workas,l1,l2⟩
      | .letE n l r z bi =>
        let ⟨l,C,workas,l1,l2⟩ ← go workas l d l1 l2 C
        let ⟨r,C,workas,l1,l2⟩ ← go workas r d l1 l2 C
        let S := l2.size
        let fv ←  worker d
        let ⟨fv,z,l1,l2⟩ ← withFreeingLet fv l r z l1 l2
        let ⟨z,C,workas,l1,l2⟩ ← go (workas.push (.fvar fv)) z (d+1) l1 l2 C
        let l2 := if (← withLCtx l1 l2 (isClass? l)).isSome then l2.patch S 1 else l2
        let R := .letE n l r z bi
        let C := C.insert e R
        return ⟨R,C,workas,l1,l2⟩
      | .proj n i l =>
        let ⟨l,C,workas,l1,l2⟩ ← go workas l d l1 l2 C
        let R := .proj n i l
        let C := C.insert e R
        return ⟨R,C,workas,l1,l2⟩
      | .mdata da l =>
        let ⟨l,C,workas,l1,l2⟩ ← go workas l d l1 l2 C
        let R := .mdata da l
        let C := C.insert e R
        return ⟨R,C,workas,l1,l2⟩
      | t => return ⟨t,C.insert e t,workas,l1,l2⟩
  do
  let ⟨r,_,_,l1,l2⟩ ← go #[] e 0 l1 l2 {}
  return ⟨r,l1,l2⟩





@[specialize,inline]
partial def Lean.Expr.onAllSubtermsWiWorkerCpsSkipTravStateTR (e : Expr) (initD : LocalContext) (initI : LocalInstances) {β: Sort _} (init : β)
  (f : Expr → Nat → β → LocalContext → LocalInstances → MetaM (Prod4 (Except Expr Expr) β LocalContext LocalInstances)) : MetaM (Prod4 Expr β LocalContext LocalInstances) :=
  trace set TracingFlags.none in
  let rec @[specialize f] go (state : β) (initD : LocalContext) (initI : LocalInstances) (ta : List Expr) (aT : AssembleTaskMeta) (up? : Bool)
  : ListProd Nat Expr → MetaM (Prod4 Expr β LocalContext LocalInstances)
    | last@(.nil) => do
      trace on .zero with s!"[onAllSubterms] empty todos ; \n  ta : {repr ta}\n  aT : {repr aT}" in
      match aT with
      | .proj n i ats =>
        match ta with
        | x :: L => go state initD initI ((.proj n i x) :: L) ats up? last
        | _ => return ⟨(failExpr "onAllSubterms"),state,initD,initI⟩
      | .mdata d ats =>
        match ta with
        | x :: L => go state initD initI ((.mdata d x) :: L) ats up? last
        | _ => return ⟨ (failExpr "onAllSubterms"),state,initD,initI⟩
      | .app ats false =>
        match ta with
        | x :: y :: L => go state initD initI ((.app y x) :: L) ats up? last
        | _ => return ⟨ (failExpr "onAllSubterms"),state,initD,initI⟩
      | .lam n i fv binfo ats false =>
        match ta with
        | x :: y :: L => do
          let X := x.abstract #[ fv]
          let initI := initI.patch binfo 1
          go state initD initI ((.lam n y X i) :: L) ats up? last
        | _ => return ⟨ (failExpr "onAllSubterms"),state,initD,initI⟩
      | .all n i fv binfo ats false =>
        match ta with
        | x :: y :: L =>  do
          let X := x.abstract #[ fv]
          let initI := initI.patch binfo 1
          go state initD initI ((.forallE n y X i) :: L) ats up? last
        | _ => return ⟨ (failExpr "onAllSubterms"),state,initD,initI⟩
      | .letE n i fv binfo ats _ =>
        match ta with
        | x :: y :: z :: L => do
          let X := x.abstract #[ fv]
          let initI := initI.patch binfo 1
          go state initD initI ((.letE n z y X i) :: L) ats up? last
        | _ => return ⟨ (failExpr "onAllSubterms"),state,initD,initI⟩
      | .nil =>
        match ta with
        | res :: _ => return ⟨res,state,initD,initI⟩
        | _ => return ⟨ (failExpr "onAllSubterms"),state,initD,initI⟩
      | _ => return ⟨ (failExpr "onAllSubterms"),state,initD,initI⟩
    | todo@(.cons depth nx more) => do
      trace on .zero with s!"[onAllSubterms] cons todos ; mode up? is {up?}" in
      if up?
      then
        trace on .zero with s!"[onAllSubterms]\n  ta : {repr ta}\n  aT : {repr aT}\n  todo : {repr todo}" in
        match aT with
        | .proj n i ats =>
          match ta with
          | x :: L => go state initD initI ((.proj n i x) :: L) ats up? todo
          | _ => return ⟨ (failExpr "onAllSubterms"),state,initD,initI⟩
        | .mdata d ats =>
          match ta with
          | x :: L => go state initD initI ((.mdata d x) :: L) ats up? todo
          | _ => return ⟨ (failExpr "onAllSubterms"),state,initD,initI⟩
        | .app ats true => go state initD initI ta (.app ats false) false todo
        | .app ats false =>
          match ta with
          | x :: y :: L => go state initD initI ((.app y x) :: L) ats up? todo
          | _ => return ⟨ (failExpr "onAllSubterms"),state,initD,initI⟩
        | .lam n i fv binfo ats true => go state initD initI ta (.lam n i fv binfo ats false) false todo
        | .lam n i fv binfo ats false =>
          match ta with
          | x :: y :: L => do
          let X := x.abstract #[ fv]
          let initI := initI.patch binfo 1
          go state initD initI ((.lam n y X i) :: L) ats up? todo
          | _ => return ⟨ (failExpr "onAllSubterms"),state,initD,initI⟩
        | .all n i fv binfo ats true => go state initD initI ta (.all n i fv binfo ats false) false todo
        | .all n i fv binfo ats false =>
          match ta with
          | x :: y :: L => do
          let X := x.abstract #[ fv]
          let initI := initI.patch binfo 1
          go state initD initI ((.forallE n y X i) :: L) ats up? todo
          | _ => return ⟨ (failExpr "onAllSubterms"),state,initD,initI⟩
        | .letE n i fv binfo ats pn =>
          if pn == 0
          then
            match ta with
            | x :: y :: z :: L => do
              let X := x.abstract #[ fv]
              let initI := initI.patch binfo 1
              go state initD initI ((.letE n z y X i) :: L) ats up? todo
            | _ => return ⟨ (failExpr "onAllSubterms"),state,initD,initI⟩
          else
            go state initD initI ta (.letE n i fv binfo ats (pn-1)) false todo
        | _ => return ⟨ (failExpr "onAllSubterms"),state,initD,initI⟩
      else do
        let here ← f nx depth state initD initI
        trace on .zero with s!"[onAllSubterms]\n  here : {repr here}\n  ta : {repr ta}\n  aT : {repr aT}\n  todo : {repr todo}" in
        let initD := here.3
        let initI := here.4
        let state := here.2
        let here := here.1
        match here with
        | .ok here =>
          match here with
          | .const _ _ | .lit _ | .mvar _ | .fvar _ | .bvar _  | .sort _ =>
              go state initD initI (here :: ta) aT true more
          | .app l r => go state initD initI ta (.app aT true) false (.cons depth l <| .cons depth r more)
          | .lam n l r i => do
            let S := initI.size
            let fv ←  worker depth
            let ⟨fv,r,initD,initI⟩ ← withFreeing fv l r initD initI
            go state initD initI ta (.lam n i (.fvar fv) S aT true) false (.cons depth l <| .cons (depth + 1) r more)
          | .forallE n l r i => do
            let S := initI.size
            let fv ← worker depth
            let ⟨fv,r,initD,initI⟩ ← withFreeing fv l r initD initI
            go state initD initI ta (.all n i (.fvar fv) S aT true) false (.cons depth l <| .cons (depth + 1) r more)
          | .letE n l r z i => do
            let S := initI.size
            let fv ←  worker depth
            let ⟨fv,z,initD,initI⟩ ← withFreeingLet fv l r z initD initI
            go state initD initI ta (.letE n i (.fvar fv) S aT 2) false (.cons depth l <| .cons depth r <| .cons (depth + 1) z more)
          | .proj n i l => go state initD initI ta (.proj n i aT) false (.cons depth l more)
          | .mdata d l => go state initD initI ta (.mdata d aT) false (.cons depth l more)
        | .error here =>
          go state initD initI (here :: ta) aT true more
  go init initD initI [] .nil false (.cons 0 e .nil)



@[specialize,inline]
partial def Lean.Expr.onAllSubtermsWiWorkerCpsSkipTravState (e : Expr) (l1 : LocalContext) (l2 : LocalInstances) {β: Sort _} (init : β)
  (f : Expr → Nat → β → LocalContext → LocalInstances → MetaM (Prod4 (Except Expr Expr) β LocalContext LocalInstances))
  : MetaM (Prod4 Expr β LocalContext LocalInstances) :=
   let rec @[specialize f] go (state : β) (e : Expr) (d : Nat) (l1 : LocalContext) (l2 : LocalInstances) (C : ExprMap Expr)
    : MetaM (Prod5 Expr (ExprMap Expr) β LocalContext LocalInstances) := do
    match C[e]? with
    | .some res => return ⟨res,C,state,l1,l2⟩
    | _ =>
      let ⟨R,state,l1,l2⟩ ← f e d state l1 l2
      match R with
      | .ok R =>
          match R with
          | .app l r =>
            let ⟨l,C,state,l1,l2⟩ ← go state l d l1 l2 C
            let ⟨r,C,state,l1,l2⟩ ← go state r d l1 l2 C
            let R := .app l r
            let C := C.insert e R
            return ⟨R,C,state,l1,l2⟩
          | .lam n l r bi =>
            let ⟨l,C,state,l1,l2⟩ ← go state l d l1 l2 C
            let S := l2.size
            let fv ←  worker d
            let ⟨_,r,l1,l2⟩ ← withFreeing fv l r l1 l2
            let ⟨r,C,state,l1,l2⟩ ← go state r (d+1) l1 l2 C
            let l2 := match bi with | .instImplicit => l2.patch S 1 | _ => l2
            let R := .lam n l r bi
            let C := C.insert e R
            return ⟨R,C,state,l1,l2⟩
          | .forallE n l r bi =>
            let ⟨l,C,state,l1,l2⟩ ← go state l d l1 l2 C
            let S := l2.size
            let fv ←  worker d
            let ⟨_,r,l1,l2⟩ ← withFreeing fv l r l1 l2
            let ⟨r,C,state,l1,l2⟩ ← go state r (d+1) l1 l2 C
            let l2 := match bi with | .instImplicit => l2.patch S 1 | _ => l2
            let R := .forallE n l r bi
            let C := C.insert e R
            return ⟨R,C,state,l1,l2⟩
          | .letE n l r z bi =>
            let ⟨l,C,state,l1,l2⟩ ← go state l d l1 l2 C
            let ⟨r,C,state,l1,l2⟩ ← go state r d l1 l2 C
            let S := l2.size
            let fv ←  worker d
            let ⟨_,z,l1,l2⟩ ← withFreeingLet fv l r z l1 l2
            let ⟨z,C,state,l1,l2⟩ ← go state z (d+1) l1 l2 C
            let l2 := if (← withLCtx l1 l2 (isClass? l)).isSome then l2.patch S 1 else l2
            let R := .letE n l r z bi
            let C := C.insert e R
            return ⟨R,C,state,l1,l2⟩
          | .proj n i l =>
            let ⟨l,C,state,l1,l2⟩ ← go state l d l1 l2 C
            let R := .proj n i l
            let C := C.insert e R
            return ⟨R,C,state,l1,l2⟩
          | .mdata da l =>
            let ⟨l,C,state,l1,l2⟩ ← go state l d l1 l2 C
            let R := .mdata da l
            let C := C.insert e R
            return ⟨R,C,state,l1,l2⟩
          | t => return ⟨t,C.insert e t,state,l1,l2⟩
      | .error R =>
          return ⟨R,C,state,l1,l2⟩
  do
  let ⟨r,_,state,l1,l2⟩ ← go init e 0 l1 l2 {}
  return ⟨r,state,l1,l2⟩





@[specialize,inline]
partial def Lean.Expr.onAllSubtermsWiWorkerTrackedCpsSkipTravStateTR (e : Expr) (initD : LocalContext) (initI : LocalInstances) {β: Sort _} (init : β)
  (f : Expr → Nat → Array Expr → β → LocalContext → LocalInstances → MetaM (Prod4 (Except Expr Expr) β LocalContext LocalInstances)) : MetaM (Prod4 Expr β LocalContext LocalInstances) :=
  trace set TracingFlags.none in
  let rec @[specialize f] go (workas : Array Expr) (state : β) (initD : LocalContext) (initI : LocalInstances) (ta : List Expr) (aT : AssembleTaskMeta) (up? : Bool)
  : ListProd Nat Expr → MetaM (Prod4 Expr β LocalContext LocalInstances)
    | last@(.nil) => do
      trace on .zero with s!"[onAllSubterms] empty todos ; \n  ta : {repr ta}\n  aT : {repr aT}" in
      match aT with
      | .proj n i ats =>
        match ta with
        | x :: L => go workas state initD initI ((.proj n i x) :: L) ats up? last
        | _ => return ⟨(failExpr "onAllSubterms"),state,initD,initI⟩
      | .mdata d ats =>
        match ta with
        | x :: L => go workas state initD initI ((.mdata d x) :: L) ats up? last
        | _ => return ⟨(failExpr "onAllSubterms"),state,initD,initI⟩
      | .app ats false =>
        match ta with
        | x :: y :: L => go workas state initD initI ((.app y x) :: L) ats up? last
        | _ => return ⟨(failExpr "onAllSubterms"),state,initD,initI⟩
      | .lam n i fv binfo ats false =>
        match ta with
        | x :: y :: L => do
          let X := x.abstract #[ fv]
          let initI := initI.patch binfo 1
          go workas state initD initI ((.lam n y X i) :: L) ats up? last
        | _ => return ⟨(failExpr "onAllSubterms"),state,initD,initI⟩
      | .all n i fv binfo ats false =>
        match ta with
        | x :: y :: L =>  do
          let X := x.abstract #[ fv]
          let initI := initI.patch binfo 1
          go workas state initD initI ((.forallE n y X i) :: L) ats up? last
        | _ => return ⟨(failExpr "onAllSubterms"),state,initD,initI⟩
      | .letE n i fv binfo ats _ =>
        match ta with
        | x :: y :: z :: L => do
          let X := x.abstract #[ fv]
          let initI := initI.patch binfo 1
          go workas state initD initI ((.letE n z y X i) :: L) ats up? last
        | _ => return ⟨(failExpr "onAllSubterms"),state,initD,initI⟩
      | .nil =>
        match ta with
        | res :: _ => return ⟨res,state,initD,initI⟩
        | _ => return ⟨(failExpr "onAllSubterms"),state,initD,initI⟩
      | _ => return ⟨(failExpr "onAllSubterms"),state,initD,initI⟩
    | todo@(.cons depth nx more) => do
      trace on .zero with s!"[onAllSubterms] cons todos ; mode up? is {up?}" in
      if up?
      then
        trace on .zero with s!"[onAllSubterms]\n  ta : {repr ta}\n  aT : {repr aT}\n  todo : {repr todo}" in
        match aT with
        | .proj n i ats =>
          match ta with
          | x :: L => go workas state initD initI ((.proj n i x) :: L) ats up? todo
          | _ => return ⟨(failExpr "onAllSubterms"),state,initD,initI⟩
        | .mdata d ats =>
          match ta with
          | x :: L => go workas state initD initI ((.mdata d x) :: L) ats up? todo
          | _ => return ⟨(failExpr "onAllSubterms"),state,initD,initI⟩
        | .app ats true => go workas state initD initI ta (.app ats false) false todo
        | .app ats false =>
          match ta with
          | x :: y :: L => go workas state initD initI ((.app y x) :: L) ats up? todo
          | _ => return ⟨(failExpr "onAllSubterms"),state,initD,initI⟩
        | .lam n i fv binfo ats true => go workas state initD initI ta (.lam n i fv binfo ats false) false todo
        | .lam n i fv binfo ats false =>
          match ta with
          | x :: y :: L => do
          let X := x.abstract #[ fv]
          let initI := initI.patch binfo 1
          go workas state initD initI ((.lam n y X i) :: L) ats up? todo
          | _ => return ⟨(failExpr "onAllSubterms"),state,initD,initI⟩
        | .all n i fv binfo ats true => go workas state initD initI ta (.all n i fv binfo ats false) false todo
        | .all n i fv binfo ats false =>
          match ta with
          | x :: y :: L => do
          let X := x.abstract #[ fv]
          let initI := initI.patch binfo 1
          go workas state initD initI ((.forallE n y X i) :: L) ats up? todo
          | _ => return ⟨(failExpr "onAllSubterms"),state,initD,initI⟩
        | .letE n i fv binfo ats pn =>
          if pn == 0
          then
            match ta with
            | x :: y :: z :: L => do
              let X := x.abstract #[ fv]
              let initI := initI.patch binfo 1
              go workas state initD initI ((.letE n z y X i) :: L) ats up? todo
            | _ => return ⟨(failExpr "onAllSubterms"),state,initD,initI⟩
          else
            go workas state initD initI ta (.letE n i fv binfo ats (pn-1)) false todo
        | _ => return ⟨(failExpr "onAllSubterms"),state,initD,initI⟩
      else do
        let here ← f nx depth workas state initD initI
        trace on .zero with s!"[onAllSubterms]\n  here : {repr here}\n  ta : {repr ta}\n  aT : {repr aT}\n  todo : {repr todo}" in
        let initD := here.3
        let initI := here.4
        let state := here.2
        let here := here.1
        match here with
        | .ok here =>
          match here with
          | .const _ _ | .lit _ | .mvar _ | .fvar _ | .bvar _  | .sort _ =>
              go workas state initD initI (here :: ta) aT true more
          | .app l r => go workas state initD initI ta (.app aT true) false (.cons depth l <| .cons depth r more)
          | .lam n l r i => do
            let S := initI.size
            let fv ←  worker depth
            let ⟨fv,r,initD,initI⟩ ← withFreeing fv l r initD initI
            let workas := workas.push (.fvar fv)
            go workas state initD initI ta (.lam n i (.fvar fv) S aT true) false (.cons depth l <| .cons (depth + 1) r more)
          | .forallE n l r i => do
            let S := initI.size
            let fv ← worker depth
            let ⟨fv,r,initD,initI⟩ ← withFreeing fv l r initD initI
            let workas := workas.push (.fvar fv)
            go workas state initD initI ta (.all n i (.fvar fv) S aT true) false (.cons depth l <| .cons (depth + 1) r more)
          | .letE n l r z i => do
            let S := initI.size
            let fv ←  worker depth
            let ⟨fv,z,initD,initI⟩ ← withFreeingLet fv l r z initD initI
            let workas := workas.push (.fvar fv)
            go workas state initD initI ta (.letE n i (.fvar fv) S aT 2) false (.cons depth l <| .cons depth r <| .cons (depth + 1) z more)
          | .proj n i l => go workas state initD initI ta (.proj n i aT) false (.cons depth l more)
          | .mdata d l => go workas state initD initI ta (.mdata d aT) false (.cons depth l more)
        | .error here =>
          go workas state initD initI (here :: ta) aT true more
  go {} init initD initI [] .nil false (.cons 0 e .nil)



@[specialize,inline]
partial def Lean.Expr.onAllSubtermsWiWorkerTrackedCpsSkipTravState (e : Expr) (l1 : LocalContext) (l2 : LocalInstances) {β: Sort _} (init : β)
  (f : Expr → Nat → Array Expr → β → LocalContext → LocalInstances → MetaM (Prod4 (Except Expr Expr) β LocalContext LocalInstances))
  : MetaM (Prod4 Expr β LocalContext LocalInstances) :=
   let rec @[specialize f] go (state : β) (workas : Array Expr) (e : Expr) (d : Nat) (l1 : LocalContext) (l2 : LocalInstances) (C : ExprMap Expr)
    : MetaM (Prod6 Expr (ExprMap Expr) (Array Expr) β LocalContext LocalInstances) := do
    match C[e]? with
    | .some res => return ⟨res,C,workas,state,l1,l2⟩
    | _ =>
      let ⟨R,state,l1,l2⟩ ← f e d workas state l1 l2
      match R with
      | .ok R =>
          match R with
          | .app l r =>
            let ⟨l,C,workas,state,l1,l2⟩ ← go state workas l d l1 l2 C
            let ⟨r,C,workas,state,l1,l2⟩ ← go state workas r d l1 l2 C
            let R := .app l r
            let C := C.insert e R
            return ⟨R,C,workas,state,l1,l2⟩
          | .lam n l r bi =>
            let ⟨l,C,workas,state,l1,l2⟩ ← go state workas l d l1 l2 C
            let S := l2.size
            let fv ←  worker d
            let ⟨fv,r,l1,l2⟩ ← withFreeing fv l r l1 l2
            let ⟨r,C,workas,state,l1,l2⟩ ← go state (workas.push (.fvar fv)) r (d+1) l1 l2 C
            let l2 := match bi with | .instImplicit => l2.patch S 1 | _ => l2
            let R := .lam n l r bi
            let C := C.insert e R
            return ⟨R,C,workas,state,l1,l2⟩
          | .forallE n l r bi =>
            let ⟨l,C,workas,state,l1,l2⟩ ← go state workas l d l1 l2 C
            let S := l2.size
            let fv ←  worker d
            let ⟨fv,r,l1,l2⟩ ← withFreeing fv l r l1 l2
            let ⟨r,C,workas,state,l1,l2⟩ ← go state (workas.push (.fvar fv)) r (d+1) l1 l2 C
            let l2 := match bi with | .instImplicit => l2.patch S 1 | _ => l2
            let R := .forallE n l r bi
            let C := C.insert e R
            return ⟨R,C,workas,state,l1,l2⟩
          | .letE n l r z bi =>
            let ⟨l,C,workas,state,l1,l2⟩ ← go state workas l d l1 l2 C
            let ⟨r,C,workas,state,l1,l2⟩ ← go state workas r d l1 l2 C
            let S := l2.size
            let fv ←  worker d
            let ⟨fv,z,l1,l2⟩ ← withFreeingLet fv l r z l1 l2
            let ⟨z,C,workas,state,l1,l2⟩ ← go state (workas.push (.fvar fv)) z (d+1) l1 l2 C
            let l2 := if (← withLCtx l1 l2 (isClass? l)).isSome then l2.patch S 1 else l2
            let R := .letE n l r z bi
            let C := C.insert e R
            return ⟨R,C,workas,state,l1,l2⟩
          | .proj n i l =>
            let ⟨l,C,workas,state,l1,l2⟩ ← go state workas l d l1 l2 C
            let R := .proj n i l
            let C := C.insert e R
            return ⟨R,C,workas,state,l1,l2⟩
          | .mdata da l =>
            let ⟨l,C,workas,state,l1,l2⟩ ← go state workas l d l1 l2 C
            let R := .mdata da l
            let C := C.insert e R
            return ⟨R,C,workas,state,l1,l2⟩
          | t => return ⟨t,C.insert e t,workas,state,l1,l2⟩
      | .error R =>
          return ⟨R,C,workas,state,l1,l2⟩
  do
  let ⟨r,_,_,state,l1,l2⟩ ← go init #[] e 0 l1 l2 {}
  return ⟨r,state,l1,l2⟩
