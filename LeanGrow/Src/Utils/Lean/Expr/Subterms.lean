
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrowBeta.Utils.Tracing
import LeanGrowBeta.Utils.Lean.LocalContext
import LeanGrowBeta.Utils.Lean.Expr.Fail
import LeanGrowBeta.Utils.LeanGrow.Nodes
import LeanGrowBeta.Data.CTrie.Basic

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

@[specialize f, inline]
partial def Lean.Expr.onAllSubtermsTR (e : Expr) (f : Expr → Expr) : Expr :=
  trace set TracingFlags.none in
  let rec @[specialize f] go (ta : List Expr) (aT : AssembleTask) (up? : Bool) : List Expr → Expr
    | last@([]) =>
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
    | todo@(nx :: more) =>
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
        let here := f nx
        trace on .zero with s!"[onAllSubterms]\n  here : {repr here}\n  ta : {repr ta}\n  aT : {repr aT}\n  todo : {repr todo}" in
        match here with
        | .const _ _ | .lit _ | .mvar _ | .fvar _ | .bvar _  | .sort _ =>
            go (here :: ta) aT true more
        | .app l r => go ta (.app aT true) false (l :: r :: more)
        | .lam n l r i => go ta (.lam n i aT true) false (l :: r :: more)
        | .forallE n l r i => go ta (.all n i aT true) false (l :: r :: more)
        | .letE n l r z i => go ta (.letE n i aT 2) false (l :: r :: z :: more)
        | .proj n i l => go ta (.proj n i aT) false (l :: more)
        | .mdata d l => go ta (.mdata d aT) false (l :: more)
  go [] .nil false [e]


@[specialize f, inline]
partial def Lean.Expr.onAllSubtermsWiDepth (e : Expr) (f : Expr → Nat → Expr) : Expr :=
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



private inductive AssembleTaskMeta where
| nil
| app (_ : AssembleTaskMeta) (post? : Bool)
| lam (_ : Name) (_ : BinderInfo) (_ : Expr) (_ : AssembleTaskMeta) (post? : Bool)
| all (_ : Name) (_ : BinderInfo) (_ : Expr) (_ : AssembleTaskMeta) (post? : Bool)
| letE (_ : Name) (_ : Bool) (_ : Expr) (_ : AssembleTaskMeta) (postNum : UInt8)
| proj (_ : Name) (_ : Nat) (_ : AssembleTaskMeta)
| mdata (_ : MData) (_ : AssembleTaskMeta)
deriving Inhabited, Repr, BEq



@[specialize f,inline]
partial def Lean.Expr.onAllSubtermsMTR (e : Expr) (initD : LocalContext) (initI : LocalInstances)
  (f : Expr → LocalContext → LocalInstances → MetaM (Prod3 Expr LocalContext LocalInstances)) : MetaM (Prod3 Expr LocalContext LocalInstances) :=
  trace set TracingFlags.none in
  let rec @[specialize f] go (initD : LocalContext) (initI : LocalInstances) (ta : List Expr) (aT : AssembleTaskMeta) (up? : Bool)
  : List Expr → MetaM (Prod3 Expr LocalContext LocalInstances)
    | last@([]) => do
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
      | .lam n i fv ats false =>
        match ta with
        | x :: y :: L => do
          let X := x.abstract #[ fv]
          go initD initI ((.lam n y X i) :: L) ats up? last
        | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
      | .all n i fv ats false =>
        match ta with
        | x :: y :: L =>  do
          let X := x.abstract #[ fv]
          go initD initI ((.forallE n y X i) :: L) ats up? last
        | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
      | .letE n i fv ats _ =>
        match ta with
        | x :: y :: z :: L => do
          let X := x.abstract #[ fv]
          go initD initI ((.letE n z y X i) :: L) ats up? last
        | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
      | .nil =>
        match ta with
        | res :: _ => return ⟨res,initD,initI⟩
        | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
      | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
    | todo@(nx :: more) => do
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
        | .lam n i fv ats true => go initD initI ta (.lam n i fv ats false) false todo
        | .lam n i fv ats false =>
          match ta with
          | x :: y :: L => do
          let X := x.abstract #[ fv]
          go initD initI ((.lam n y X i) :: L) ats up? todo
          | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
        | .all n i fv ats true => go initD initI ta (.all n i fv ats false) false todo
        | .all n i fv ats false =>
          match ta with
          | x :: y :: L => do
          let X := x.abstract #[ fv]
          go initD initI ((.forallE n y X i) :: L) ats up? todo
          | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
        | .letE n i fv ats pn =>
          if pn == 0
          then
            match ta with
            | x :: y :: z :: L => do
              let X := x.abstract #[ fv]
              go initD initI ((.letE n z y X i) :: L) ats up? todo
            | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
          else
            go initD initI ta (.letE n i fv ats (pn-1)) false todo
        | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
      else do
        let here ← f nx initD initI
        trace on .zero with s!"[onAllSubterms]\n  here : {repr here}\n  ta : {repr ta}\n  aT : {repr aT}\n  todo : {repr todo}" in
        let initD := here.2
        let initI := here.3
        let here := here.1
        match here with
        | .const _ _ | .lit _ | .mvar _ | .fvar _ | .bvar _  | .sort _ =>
            go initD initI (here :: ta) aT true more
        | .app l r => go initD initI ta (.app aT true) false (l :: r :: more)
        | .lam n l r i => do
          let fv ← mkFreshId
          let ⟨fv,r,initD,initI⟩ ← withFreeing fv l r initD initI
          go initD initI ta (.lam n i (.fvar fv) aT true) false (l :: r :: more)
        | .forallE n l r i => do
          let fv ← mkFreshId
          let ⟨fv,r,initD,initI⟩ ← withFreeing fv l r initD initI
          go initD initI ta (.all n i (.fvar fv) aT true) false (l :: r :: more)
        | .letE n l r z i => do
          let fv ← mkFreshId
          let ⟨fv,z,initD,initI⟩ ← withFreeingLet fv l r z initD initI
          go initD initI ta (.letE n i (.fvar fv) aT 2) false (l :: r :: z :: more)
        | .proj n i l => go initD initI ta (.proj n i aT) false (l :: more)
        | .mdata d l => go initD initI ta (.mdata d aT) false (l :: more)
  go initD initI [] .nil false [e]


/--
For `f`, we conserder bvar i loose if i ≥ d
-/
@[specialize f, inline]
partial def Lean.Expr.onAllSubtermsWiWorker (e : Expr) (initD : LocalContext) (initI : LocalInstances)
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
      | .lam n i fv ats false =>
        match ta with
        | x :: y :: L => do
          let X := x.abstract #[ fv]
          go initD initI ((.lam n y X i) :: L) ats up? last
        | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
      | .all n i fv ats false =>
        match ta with
        | x :: y :: L =>  do
          let X := x.abstract #[ fv]
          go initD initI ((.forallE n y X i) :: L) ats up? last
        | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
      | .letE n i fv ats _ =>
        match ta with
        | x :: y :: z :: L => do
          let X := x.abstract #[ fv]
          go initD initI ((.letE n z y X i) :: L) ats up? last
        | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
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
        | .lam n i fv ats true => go initD initI ta (.lam n i fv ats false) false todo
        | .lam n i fv ats false =>
          match ta with
          | x :: y :: L => do
          let X := x.abstract #[ fv]
          go initD initI ((.lam n y X i) :: L) ats up? todo
          | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
        | .all n i fv ats true => go initD initI ta (.all n i fv ats false) false todo
        | .all n i fv ats false =>
          match ta with
          | x :: y :: L => do
          let X := x.abstract #[ fv]
          go initD initI ((.forallE n y X i) :: L) ats up? todo
          | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
        | .letE n i fv ats pn =>
          if pn == 0
          then
            match ta with
            | x :: y :: z :: L => do
              let X := x.abstract #[ fv]
              go initD initI ((.letE n z y X i) :: L) ats up? todo
            | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
          else
            go initD initI ta (.letE n i fv ats (pn-1)) false todo
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
          let fv ←  worker depth
          let ⟨fv,r,initD,initI⟩ ← withFreeing fv l r initD initI
          go initD initI ta (.lam n i (.fvar fv) aT true) false (.cons depth l <| .cons (depth + 1) r more)
        | .forallE n l r i => do
          let fv ←  worker depth
          let ⟨fv,r,initD,initI⟩ ← withFreeing fv l r initD initI
          go initD initI ta (.all n i (.fvar fv) aT true) false (.cons depth l <| .cons (depth + 1) r more)
        | .letE n l r z i => do
          let fv ←  worker depth
          let ⟨fv,z,initD,initI⟩ ← withFreeingLet fv l r z initD initI
          go initD initI ta (.letE n i (.fvar fv) aT 2) false (.cons depth l <| .cons depth r <| .cons (depth + 1) z more)
        | .proj n i l => go initD initI ta (.proj n i aT) false (.cons depth l more)
        | .mdata d l => go initD initI ta (.mdata d aT) false (.cons depth l more)
  go initD initI [] .nil false (.cons 0 e .nil)


@[specialize f, inline]
partial def Lean.Expr.onAllSubtermsWiWorkerTracked (e : Expr) (initD : LocalContext) (initI : LocalInstances)
  (f : Expr → Nat → CTrie Unit → LocalContext → LocalInstances → MetaM (Prod3 Expr LocalContext LocalInstances)) : MetaM (Prod3 Expr LocalContext LocalInstances) :=
  trace set TracingFlags.none in
  let rec @[specialize f] go (workas : CTrie Unit) (initD : LocalContext) (initI : LocalInstances) (ta : List Expr) (aT : AssembleTaskMeta) (up? : Bool)
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
      | .lam n i fv ats false =>
        match ta with
        | x :: y :: L => do
          let X := x.abstract #[ fv]
          go workas initD initI ((.lam n y X i) :: L) ats up? last
        | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
      | .all n i fv ats false =>
        match ta with
        | x :: y :: L =>  do
          let X := x.abstract #[ fv]
          go workas initD initI ((.forallE n y X i) :: L) ats up? last
        | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
      | .letE n i fv ats _ =>
        match ta with
        | x :: y :: z :: L => do
          let X := x.abstract #[ fv]
          go workas initD initI ((.letE n z y X i) :: L) ats up? last
        | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
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
        | .lam n i fv ats true => go workas initD initI ta (.lam n i fv ats false) false todo
        | .lam n i fv ats false =>
          match ta with
          | x :: y :: L => do
          let X := x.abstract #[ fv]
          go workas initD initI ((.lam n y X i) :: L) ats up? todo
          | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
        | .all n i fv ats true => go workas initD initI ta (.all n i fv ats false) false todo
        | .all n i fv ats false =>
          match ta with
          | x :: y :: L => do
          let X := x.abstract #[ fv]
          go workas initD initI ((.forallE n y X i) :: L) ats up? todo
          | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
        | .letE n i fv ats pn =>
          if pn == 0
          then
            match ta with
            | x :: y :: z :: L => do
              let X := x.abstract #[ fv]
              go workas initD initI ((.letE n z y X i) :: L) ats up? todo
            | _ => return ⟨failExpr "onAllSubterms",initD,initI⟩
          else
            go workas initD initI ta (.letE n i fv ats (pn-1)) false todo
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
          let fv ←  worker depth
          let workas := workas.insert fv.toString.toUTF8 ()
          let ⟨fv,r,initD,initI⟩ ← withFreeing fv l r initD initI
          go workas initD initI ta (.lam n i (.fvar fv) aT true) false (.cons depth l <| .cons (depth + 1) r more)
        | .forallE n l r i => do
          let fv ←  worker depth
          let workas := workas.insert fv.toString.toUTF8 ()
          let ⟨fv,r,initD,initI⟩ ← withFreeing fv l r initD initI
          go workas initD initI ta (.all n i (.fvar fv) aT true) false (.cons depth l <| .cons (depth + 1) r more)
        | .letE n l r z i => do
          let fv ←  worker depth
          let workas := workas.insert fv.toString.toUTF8 ()
          let ⟨fv,z,initD,initI⟩ ← withFreeingLet fv l r z initD initI
          go workas initD initI ta (.letE n i (.fvar fv) aT 2) false (.cons depth l <| .cons depth r <| .cons (depth + 1) z more)
        | .proj n i l => go workas initD initI ta (.proj n i aT) false (.cons depth l more)
        | .mdata d l => go workas initD initI ta (.mdata d aT) false (.cons depth l more)
  go {} initD initI [] .nil false (.cons 0 e .nil)






@[specialize,inline]
partial def Lean.Expr.onAllSubtermsWiWorkerCpsSkipTravState (e : Expr) (initD : LocalContext) (initI : LocalInstances) {β: Sort _} (init : β)
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
      | .lam n i fv ats false =>
        match ta with
        | x :: y :: L => do
          let X := x.abstract #[ fv]
          go state initD initI ((.lam n y X i) :: L) ats up? last
        | _ => return ⟨ (failExpr "onAllSubterms"),state,initD,initI⟩
      | .all n i fv ats false =>
        match ta with
        | x :: y :: L =>  do
          let X := x.abstract #[ fv]
          go state initD initI ((.forallE n y X i) :: L) ats up? last
        | _ => return ⟨ (failExpr "onAllSubterms"),state,initD,initI⟩
      | .letE n i fv ats _ =>
        match ta with
        | x :: y :: z :: L => do
          let X := x.abstract #[ fv]
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
        | .lam n i fv ats true => go state initD initI ta (.lam n i fv ats false) false todo
        | .lam n i fv ats false =>
          match ta with
          | x :: y :: L => do
          let X := x.abstract #[ fv]
          go state initD initI ((.lam n y X i) :: L) ats up? todo
          | _ => return ⟨ (failExpr "onAllSubterms"),state,initD,initI⟩
        | .all n i fv ats true => go state initD initI ta (.all n i fv ats false) false todo
        | .all n i fv ats false =>
          match ta with
          | x :: y :: L => do
          let X := x.abstract #[ fv]
          go state initD initI ((.forallE n y X i) :: L) ats up? todo
          | _ => return ⟨ (failExpr "onAllSubterms"),state,initD,initI⟩
        | .letE n i fv ats pn =>
          if pn == 0
          then
            match ta with
            | x :: y :: z :: L => do
              let X := x.abstract #[ fv]
              go state initD initI ((.letE n z y X i) :: L) ats up? todo
            | _ => return ⟨ (failExpr "onAllSubterms"),state,initD,initI⟩
          else
            go state initD initI ta (.letE n i fv ats (pn-1)) false todo
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
            let fv ←  worker depth
            let ⟨fv,r,initD,initI⟩ ← withFreeing fv l r initD initI
            go state initD initI ta (.lam n i (.fvar fv) aT true) false (.cons depth l <| .cons (depth + 1) r more)
          | .forallE n l r i => do
            let fv ← worker depth
            let ⟨fv,r,initD,initI⟩ ← withFreeing fv l r initD initI
            go state initD initI ta (.all n i (.fvar fv) aT true) false (.cons depth l <| .cons (depth + 1) r more)
          | .letE n l r z i => do
            let fv ←  worker depth
            let ⟨fv,z,initD,initI⟩ ← withFreeingLet fv l r z initD initI
            go state initD initI ta (.letE n i (.fvar fv) aT 2) false (.cons depth l <| .cons depth r <| .cons (depth + 1) z more)
          | .proj n i l => go state initD initI ta (.proj n i aT) false (.cons depth l more)
          | .mdata d l => go state initD initI ta (.mdata d aT) false (.cons depth l more)
        | .error here =>
          go state initD initI (here :: ta) aT true more
  go init initD initI [] .nil false (.cons 0 e .nil)



@[specialize,inline]
partial def Lean.Expr.onAllSubtermsWiWorkerTrackedCpsSkipTravState (e : Expr) (initD : LocalContext) (initI : LocalInstances) {β: Sort _} (init : β)
  (f : Expr → Nat → CTrie Unit → β → LocalContext → LocalInstances → MetaM (Prod4 (Except Expr Expr) β LocalContext LocalInstances)) : MetaM (Prod4 Expr β LocalContext LocalInstances) :=
  trace set TracingFlags.none in
  let rec @[specialize f] go (workas : CTrie Unit) (state : β) (initD : LocalContext) (initI : LocalInstances) (ta : List Expr) (aT : AssembleTaskMeta) (up? : Bool)
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
      | .lam n i fv ats false =>
        match ta with
        | x :: y :: L => do
          let X := x.abstract #[ fv]
          go workas state initD initI ((.lam n y X i) :: L) ats up? last
        | _ => return ⟨(failExpr "onAllSubterms"),state,initD,initI⟩
      | .all n i fv ats false =>
        match ta with
        | x :: y :: L =>  do
          let X := x.abstract #[ fv]
          go workas state initD initI ((.forallE n y X i) :: L) ats up? last
        | _ => return ⟨(failExpr "onAllSubterms"),state,initD,initI⟩
      | .letE n i fv ats _ =>
        match ta with
        | x :: y :: z :: L => do
          let X := x.abstract #[ fv]
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
        | .lam n i fv ats true => go workas state initD initI ta (.lam n i fv ats false) false todo
        | .lam n i fv ats false =>
          match ta with
          | x :: y :: L => do
          let X := x.abstract #[ fv]
          go workas state initD initI ((.lam n y X i) :: L) ats up? todo
          | _ => return ⟨(failExpr "onAllSubterms"),state,initD,initI⟩
        | .all n i fv ats true => go workas state initD initI ta (.all n i fv ats false) false todo
        | .all n i fv ats false =>
          match ta with
          | x :: y :: L => do
          let X := x.abstract #[ fv]
          go workas state initD initI ((.forallE n y X i) :: L) ats up? todo
          | _ => return ⟨(failExpr "onAllSubterms"),state,initD,initI⟩
        | .letE n i fv ats pn =>
          if pn == 0
          then
            match ta with
            | x :: y :: z :: L => do
              let X := x.abstract #[ fv]
              go workas state initD initI ((.letE n z y X i) :: L) ats up? todo
            | _ => return ⟨(failExpr "onAllSubterms"),state,initD,initI⟩
          else
            go workas state initD initI ta (.letE n i fv ats (pn-1)) false todo
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
            let fv ←  worker depth
            let workas := workas.insert fv.toString.toUTF8 ()
            let ⟨fv,r,initD,initI⟩ ← withFreeing fv l r initD initI
            go workas state initD initI ta (.lam n i (.fvar fv) aT true) false (.cons depth l <| .cons (depth + 1) r more)
          | .forallE n l r i => do
            let fv ← worker depth
            let workas := workas.insert fv.toString.toUTF8 ()
            let ⟨fv,r,initD,initI⟩ ← withFreeing fv l r initD initI
            go workas state initD initI ta (.all n i (.fvar fv) aT true) false (.cons depth l <| .cons (depth + 1) r more)
          | .letE n l r z i => do
            let fv ←  worker depth
            let workas := workas.insert fv.toString.toUTF8 ()
            let ⟨fv,z,initD,initI⟩ ← withFreeingLet fv l r z initD initI
            go workas state initD initI ta (.letE n i (.fvar fv) aT 2) false (.cons depth l <| .cons depth r <| .cons (depth + 1) z more)
          | .proj n i l => go workas state initD initI ta (.proj n i aT) false (.cons depth l more)
          | .mdata d l => go workas state initD initI ta (.mdata d aT) false (.cons depth l more)
        | .error here =>
          go workas state initD initI (here :: ta) aT true more
  go {} init initD initI [] .nil false (.cons 0 e .nil)
