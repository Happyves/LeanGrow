/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Lean
import LeanGrow.Src.Data.Amalgames
import LeanGrow.Src.Data.CTrie.Basic
import LeanGrow.Src.Utils.Tracing
import LeanGrow.Src.Utils.Lean.Expr.Basic
import LeanGrow.Src.Utils.Lean.MetaAPI

open Lean Meta


def Lean.Name.isSimpTheorem : Name → Bool
  | .str _ post => String.isPrefixOf "_simp" post
  | _ => false

def Lean.Name.delabSimpTheorem : Name → Option Name
  | .str real post => if String.isPrefixOf "_simp" post then .some real else .none
  | _ => .none


#check id

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
partial def Lean.Expr.onAllSubtermsWiDepthSkip (e : Expr) (f : Expr → Nat → Except Expr Expr) : Expr :=
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
        match here with
        | .error here =>
          go (here :: ta) aT true more
        | .ok here =>
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



def Lean.Expr.beta1Spe : Expr → Expr
  | .app (.lam _ _ b _ ) a => b.onAllSubtermsWiDepthSkip (fun e d =>
    match e with
    | .bvar D =>
      if d == D then .error a else .ok e
    | _ => .ok e
    )
  | x => x


def Lean.Expr.beta1 : Expr → Expr
  | .app (.lam _ _ b _ ) a => Expr.instantiate1 b a
  | x => x


-- #eval Lean.Expr.beta1 <| Expr.app (.lam `a (.const `x []) (.forallE `b (.const `x []) (.bvar 1) .default) .default) (.bvar 0)
-- #eval Lean.Expr.beta1Spe <| Expr.app (.lam `a (.const `x []) (.forallE `b (.const `x []) (.bvar 1) .default) .default) (.bvar 0)
-- insatnciate also bumps bvar idx in subst



def delab_simpTheorem
  (l1 : LocalContext) (l2 : LocalInstances)
  (terminal : Bool) (proof topType : Expr) (extFvs : List FVarId)
  (sofar : ListProd3 (List FVarId) Expr Expr) (binFvs : Array Expr) : MetaM (Option (ListProd3 (List FVarId) Expr Expr)) := do
  mtracing
  let T ← InferType proof l1 l2
  mtrace on .zero with s!" on type {← ppExpr T}"
  match T.eq?, T.iff? with
  | .some (_,lhs,_), _ | _, .some (lhs,_) =>
    -- let .mk _ actFvs ←  lhs.collectFVars.run {}
    -- let actFvs := actFvs.fvarIds
    -- let binFvs := binFvs.filter (fun x => actFvs.contains x.fvarId!)
    let patToSimp := Expr.beta1Spe (.app topType (Expr.abstract lhs binFvs))
    let patToSimp := patToSimp.headBeta
    mtrace on .zero with s!" topType : {← ppExpr topType}\n binFvs : {← binFvs.mapM ppExpr}\n patToSimp : {← ppExpr patToSimp}"
    if terminal
    then
      let .const n _ := proof.getAppFn' | return .some sofar
      if n == ``eq_true || n == ``eq_false
      then
        mtrace on .zero with s!" adding\nType : {← ppExpr patToSimp}\nSubproof : {← ppExpr (proof.getArg! 1)}"
        mtrace on .one with s!" Raw\n {repr patToSimp}"
        return .some <| .cons extFvs patToSimp (proof.getArg! 1) sofar
      else
        mtrace on .zero with s!" adding\nType : {← ppExpr patToSimp}\nSubproof : {← ppExpr proof}"
        return .some <| .cons extFvs patToSimp proof sofar -- for stuff like `iff_self` `lt_self_iff_false` ...
    else
      mtrace on .zero with s!" adding\nType : {← ppExpr patToSimp}\nSubproof : {← ppExpr proof}"
      mtrace on .one with s!" Raw\n {repr patToSimp}"
      return .some <| .cons extFvs patToSimp proof sofar
  | .none, .none =>
      return .none
    -- return .some <|  .cons extFvs T proof sofar
    -- -- can originate from `simpa using ...` as in `ConvexCone.salient_positive`



#check eq_true
#check eq_false


#check SimpCongrTheorem


def delab_simpCongrTheorem?
  (l1 : LocalContext) (l2 : LocalInstances)
  (preProcessed : CTrie SimpCongrTheorem)
  (proof topType : Expr) (extFvs : List FVarId)
  (sofar : ListProd3 (List FVarId) Expr Expr) (binFvs : Array Expr) : MetaM (OptionProd (ListProd3 (List FVarId) Expr Expr) (Array ((List FVarId) × Expr))) := do
  mtracing
  let .const n _:= proof.getAppFn' | return .none
  mtrace on .zero with s!" n : {n}"
  match preProcessed.find? n.toString.toUTF8 with
  | .none => return .none
  | .some thm =>
      let T ← InferType proof l1 l2
      let lhs ← (do
        match T.eq? with
        | .some (_,lhs,_) => return Option.some lhs
        | .none =>
            match T.iff? with
            | .some (lhs,_) => return .some lhs
            | _ => return .none
        )
      mtrace on .zero with s!"lhs  {← lhs.mapM ppExpr}"
      let .some lhs := lhs | return .none
      -- let .mk _ actFvs ← lhs.collectFVars.run {}
      -- let actFvs := actFvs.fvarIds
      -- let binFvs := binFvs.filter (fun x => actFvs.contains x.fvarId!)
      let patToSimp := Expr.beta1Spe (.app topType (Expr.abstract lhs binFvs))
      let patToSimp := patToSimp.headBeta
      mtrace on .zero with s!" adding with\ntopType : {← ppExpr topType}\n binFvs : {← binFvs.mapM ppExpr}\n patToSimp : {← ppExpr patToSimp}"
      let sofar := .cons extFvs patToSimp proof sofar
      let as := proof.getAppArgs
      let ps := thm.hypothesesPos.map (fun i => (extFvs, as[i]!))
      mtrace on .zero with s!"ps fv : {repr <| ps.map (fun x => x.1)} \nps terms  {← ps.mapM (fun x => ppExpr x.2)}"
      -- Long term todo: find out if hyps dependent, and do split only if they are.
      -- Otherwise, find way to carry out one simp after the other
      return .some sofar ps

#check iff_of_eq
#check Iff.of_eq

partial def consumeAndProjs (e : Expr) : Expr :=
  match e.getAppFn' with
  | .const n _ =>
    if n == ``And.left || n == ``And.right
    then consumeAndProjs (e.getArg! 2)
    else e
  | _ => e

#check 1

partial def delab_simpStep
  (l1 : LocalContext) (l2 : LocalInstances)
  (preProcessed : CTrie SimpCongrTheorem)
  (terminal : Bool) (proof topType : Expr) (extFvs : List FVarId)
  (sofar : ListProd3 (List FVarId) Expr Expr) (binFvs : Array Expr) : MetaM (OptionProd4 (ListProd3 (List FVarId) Expr Expr) (Array (ListProd3 (List FVarId) Expr Expr)) LocalContext LocalInstances) := do
  mtracing
  let rec @[inline] baseCase (l1 : LocalContext) (l2 : LocalInstances) (proof : Expr)
  : MetaM (OptionProd4 (ListProd3 (List FVarId) Expr Expr) (Array (ListProd3 (List FVarId) Expr Expr)) LocalContext LocalInstances) := do
    mtrace on .zero with s!" base case with terminal {terminal}"
    if terminal
    then
      let .some res ← delab_simpTheorem l1 l2 terminal proof topType extFvs sofar binFvs | return .none
      return .some res #[] l1 l2
    else
      let res ← delab_simpCongrTheorem? l1 l2 preProcessed proof topType extFvs sofar binFvs
      match res with
      | .none =>
        let .some res ← delab_simpTheorem l1 l2 terminal proof topType extFvs sofar binFvs | return .none
        return .some res #[] l1 l2
      | .some sofar next =>
          let mut congrSplits := #[]
          let mut L1 := l1
          let mut L2 := l2
          for (extFvs, argProof) in next do
            mtrace on .zero with s!" congr split\nType : {← ppExpr (← InferType argProof l1 l2)}\nTerm : {← ppExpr argProof}"
            match argProof with
            | .lam .. =>
                let .mk argProof nfv l1 l2 ← LambdaLetTelescope argProof 0 L1 L2
                let real :=
                  match argProof.getAppFn' with
                  | .const n _ =>
                      if n == ``Iff.of_eq || n == ``iff_of_eq
                      then argProof.getArg! 2
                      else argProof
                  | _ => argProof
                let extFvs := nfv.foldl (fun x y => y.fvarId! :: x) extFvs
                let extFvs := binFvs.foldl (fun x y => y.fvarId! :: x) extFvs
                let inter ← delab_simpStep l1 l2 preProcessed false real (.lam `simpParse (.const `falseButOk []) (.bvar 0) .default) extFvs .nil #[]
                let .some ted lif l1 l2 := inter | return .none
                congrSplits := congrSplits ++ (lif.push ted)
                L1 := l1
                L2 := l2
            | _ =>
              let real :=
                match argProof.getAppFn' with
                | .const n _ =>
                    if n == ``Iff.of_eq || n == ``iff_of_eq
                    then argProof.getArg! 2
                    else argProof
                | _ => argProof
              let extFvs := binFvs.foldl (fun x y => y.fvarId! :: x) extFvs
              let inter ← delab_simpStep L1 L2 preProcessed false real (.lam `simpParse (.const `falseButOk []) (.bvar 0) .default) extFvs .nil #[]
              let .some ted lif l1 l2 := inter | return .none
              congrSplits := congrSplits ++ (lif.push ted)
              L1 := l1
              L2 := l2
          return .some sofar congrSplits L1 L2
  mtrace on .two with s!" going with topType {← ppExpr topType}"
  mtrace on .three with s!" binFvs : {← binFvs.mapM ppExpr}\n extFvs : {← withLCtx l1 l2 <| extFvs.mapM FVarId.getUserName}"
  mtrace on .one with s!" going on proof {← ppExpr proof}"
  match proof.getAppFn' with
  | .const h _ =>
      match h with
      | ``Eq.trans => do -- trans
        let as := proof.getAppArgs
        let .some inter lif1 l1 l2 ← delab_simpStep l1 l2 preProcessed false as[4]! topType extFvs sofar binFvs | return .none
        let .some res lif2 l1 l2 ← delab_simpStep l1 l2 preProcessed terminal as[5]! topType extFvs inter binFvs | return .none
        return .some res (lif1 ++ lif2) l1 l2
      | ``congrFun => --congrFun
        let as := proof.getAppArgs
        let a0 := Expr.abstract as[0]! binFvs
        let a5 := Expr.abstract as[5]! binFvs
        let newTop : Expr := .lam `simpParse a0 (Expr.beta1Spe (.app topType (.app (.bvar binFvs.size) a5))) .default
        delab_simpStep l1 l2 preProcessed terminal as[4]! newTop extFvs sofar binFvs
      | ``congr => do -- congr
        let as := proof.getAppArgs
        let a0 := Expr.abstract as[0]! binFvs
        let a1 := Expr.abstract as[1]! (binFvs.push (.fvar ⟨`dummy⟩))
        let a4 := Expr.abstract as[4]! binFvs
        let newTop : Expr := .lam `simpParse (.forallE `simpParse a0 a1 .default) (Expr.beta1Spe (.app topType (.app (.bvar binFvs.size) a4))) .default
        let .some inter lif1 l1 l2 ← delab_simpStep l1 l2 preProcessed terminal as[6]! newTop extFvs sofar binFvs | return .none
        let a3 := Expr.abstract as[3]! binFvs
        let newTop : Expr := .lam `simpParse a0 (Expr.beta1Spe (.app topType (.app a3 (.bvar binFvs.size)))) .default
        let .some res lif2 l1 l2 ← delab_simpStep l1 l2 preProcessed terminal as[7]! newTop extFvs inter binFvs | return .none
        return .some res (lif1 ++ lif2) l1 l2
      | ``propext => -- propext
        let p' := proof.getArg! 2
        baseCase l1 l2 p'
      | ``congrArg => -- congrArg
        let as := proof.getAppArgs
        let a0 := Expr.abstract as[0]! binFvs
        let a1 := Expr.abstract as[1]! (binFvs.push (.fvar ⟨`dummy⟩))
        let a4 := Expr.abstract as[4]! binFvs
        let newTop : Expr := .lam `simpParse  (.forallE `simpParse a0 a1 .default) (Expr.beta1Spe (.app topType (.app a4 (.bvar binFvs.size)))) .default
        delab_simpStep l1 l2 preProcessed terminal as[5]! newTop extFvs sofar binFvs
      | ``implies_congr => do --implies_congr
        let as := proof.getAppArgs
        let P ← InferType as[0]! l1 l2
        let Q ← InferType as[2]! l1 l2
        let a2 := Expr.abstract as[2]! (binFvs.push (.fvar ⟨`dummy⟩))
        let newTop : Expr := .lam `simpParse P (Expr.beta1Spe (.app topType (.forallE `simpParse (.bvar binFvs.size) a2 .default))) .default
        let .some inter lif1 l1 l2 ← delab_simpStep l1 l2 preProcessed terminal as[4]! newTop extFvs sofar binFvs | return .none
        let a1 := Expr.abstract as[1]! binFvs
        let newTop : Expr := .lam `simpParse Q (Expr.beta1Spe (.app topType (.forallE `simpParse a1 (.bvar (binFvs.size + 1)) .default))) .default
        let .some res lif2 l1 l2 ← delab_simpStep l1 l2 preProcessed terminal as[5]! newTop extFvs inter binFvs | return .none
        return .some res (lif1 ++ lif2) l1 l2
      | ``implies_congr_ctx => do --implies_congr_ctx
        let as := proof.getAppArgs
        match as[5]! with
        | .lam _ _ nx _ =>
          let a2 := Expr.abstract as[2]! (binFvs.push (.fvar ⟨`dummy⟩))
          let newTop : Expr := .lam `simpParse (.sort 0) (Expr.beta1Spe (.app topType (.forallE `simpParse (.bvar binFvs.size) a2 .default))) .default
          let .some inter lif1 l1 l2 ← delab_simpStep l1 l2 preProcessed terminal as[4]! newTop extFvs sofar binFvs | return .none
          let a1 := Expr.abstract as[1]! binFvs
          let newTop : Expr := .lam `simpParse (.sort 0) (Expr.beta1Spe (.app topType (.forallE `simpParse a1 (.bvar (binFvs.size + 1)) .default))) .default
          let .some res lif2 l1 l2 ← delab_simpStep l1 l2 preProcessed terminal nx newTop extFvs inter binFvs | return .none
          return .some res (lif1 ++ lif2) l1 l2
        | _ =>
          mtrace on .zero with s!"At proof of type:\n{← ppExpr <| ← InferType proof l1 l2}\nAnd of value:\n{← ppExpr proof}\nExpected subproof ↓ to be a λ:\n{← ppExpr as[5]!}"
          return .none
      | ``implies_dep_congr_ctx => do --implies_dep_congr_ctx
        let as := proof.getAppArgs
        match as[5]! with
        | .lam _ _ nx _ => do
          let a2 := Expr.abstract as[2]! (binFvs.push (.fvar ⟨`dummy⟩))
          let newTop : Expr := .lam `simpParse (.sort 0) (Expr.beta1Spe (.app topType (.forallE `simpParse (.bvar binFvs.size) a2 .default))) .default
          let .some inter lif1 l1 l2 ← delab_simpStep l1 l2 preProcessed terminal as[3]! newTop extFvs sofar binFvs | return .none
          let a1 := Expr.abstract as[1]! binFvs
          let newTop : Expr := .lam `simpParse (.sort 0) (Expr.beta1Spe (.app topType (.forallE `simpParse a1 (.app (.bvar (binFvs.size + 1)) (.bvar binFvs.size)) .default))) .default
          let .mk fv l1 l2 ← WithLocalDecl (`simpParse ++ (← mkFreshId)) as[1]! l1 l2
          let fv := .fvar fv
          let nx := nx.instantiate1 fv
          let .some res lif2 l1 l2 ← delab_simpStep l1 l2 preProcessed terminal nx newTop extFvs inter (binFvs.push fv) | return .none
          return .some res (lif1 ++ lif2) l1 l2
        | _ =>
          mtrace on .zero with  s!"[delab_simpStep preProcessed] At proof of type:\n{← ppExpr <| ← InferType proof l1 l2}\nAnd of value:\n{← ppExpr proof}\nExpected subproof ↓ to be a λ:\n{← ppExpr as[5]!}"
          return .none
      | ``forall_prop_domain_congr => do --forall_prop_domain_congr
        let as := proof.getAppArgs
        match as[5]! with
        | .lam _ _ nx _ =>
          let .some (_,lhs,rhs) := (← InferType proof  l1 l2).eq? | (do mtrace on .zero with s!"[delab_simpStep preProcessed] 1" ; return .none)
          let sofar : ListProd3 (List FVarId) Expr Expr :=
            if terminal
            then .cons extFvs (Expr.beta1Spe (.app topType (Expr.abstract lhs binFvs))) proof sofar
            else .cons extFvs (Expr.beta1Spe (.app topType (Expr.abstract rhs binFvs))) proof sofar
          let extFvs := binFvs.foldl (fun x y => y.fvarId! :: x) extFvs
          let .some inter lif1 l1 l2 ← delab_simpStep l1 l2 preProcessed terminal as[4]! (.lam `simpParse (.sort 0) (.bvar 0) .default) extFvs sofar #[] | return .none
          let .mk fv l1 l2 ← WithLocalDecl (`simpParse ++ (← mkFreshId)) as[1]! l1 l2
          let fv := .fvar fv
          let nx := nx.instantiate1 fv
          let a1 := Expr.abstract as[1]! binFvs
          let .some res lif2 l1 l2 ← delab_simpStep l1 l2 preProcessed terminal nx (.lam `simpParse (.sort 0) (.forallE `simpParse a1 (.bvar 1) .default) .default) extFvs inter #[fv] | return .none
          return .some res (lif1 ++ lif2) l1 l2
        | _ =>
          mtrace on .zero with s!"[delab_simpStep preProcessed] At proof of type:\n{← ppExpr <| ← InferType proof l1 l2}\nAnd of value:\n{← ppExpr proof}\nExpected subproof ↓ to be a λ:\n{← ppExpr as[5]!}"
          return .none
      | ``forall_congr => do --forall_congr
        let as := proof.getAppArgs
        match as[3]! with
        | .lam _ _ nx _ =>
          let .mk fv l1 l2 ← WithLocalDecl (`simpParse ++ (← mkFreshId)) as[0]! l1 l2
          let fv := .fvar fv
          let nx := nx.instantiate1 fv
          let a0 := Expr.abstract as[0]! binFvs
          delab_simpStep l1 l2 preProcessed terminal nx (.lam `simpParse (.sort 0) (Expr.beta1Spe (.app topType (.forallE `simpParse a0 ((.bvar (binFvs.size + 1))) .default))) .default) extFvs sofar (binFvs.push fv)
        | _ =>
          mtrace on .zero with s!"[delab_simpStep preProcessed] At proof of type:\n{← ppExpr <| ← InferType proof l1 l2}\nAnd of value:\n{← ppExpr proof}\nExpected subproof ↓ to be a λ:\n{← ppExpr as[3]!}"
          return .none
      | ``funext => do --funext
        let as := proof.getAppArgs
        match as[4]! with
        | .lam _ _ nx _ =>
          let .mk fv l1 l2 ← WithLocalDecl (`simpParse ++ (← mkFreshId)) as[0]! l1 l2
          let fv := .fvar fv
          let nx := nx.instantiate1 fv
          let a1 := Expr.abstract as[1]! binFvs
          let a0 := Expr.abstract as[0]! binFvs
          delab_simpStep l1 l2 preProcessed terminal nx (.lam `simpParse (.app a1 fv) (Expr.beta1Spe (.app topType (.lam `simpParse a0 ((.bvar (binFvs.size + 1))) .default))) .default) extFvs sofar (binFvs.push fv)
          -- introduces eta expantion in topType ; the type ↑ is incorrect, but we don't care as the purpose
          -- of topType is to get beta'ed anyway ?!?
        | _ =>
          mtrace on .zero with s!"[delab_simpStep preProcessed] At proof of type:\n{← ppExpr <| ← InferType proof l1 l2}\nAnd of value:\n{← ppExpr proof}\nExpected subproof ↓ to be a λ:\n{← ppExpr as[4]!}"
          return .none
      | ``Eq.ndrec => do --Eq.ndrec
        let as := proof.getAppArgs
        match as[2]! with -- motive
        | .lam n t proj_eq b => -- expected to be `fun x => a.i = x.i`
            let .some (_,_,rhs) := proj_eq.eq? | (do mtrace on .zero with s!"[delab_simpStep preProcessed] At proof of type:\n{← ppExpr <| ← InferType proof l1 l2}\nAnd of value:\n{← ppExpr proof}\nExpected motive ↓ to be a =:\n{← ppExpr proj_eq}" ; return .none)
            let rhs := Expr.abstract rhs binFvs
            delab_simpStep l1 l2 preProcessed terminal as[5]! (.lam n t (Expr.beta1Spe (.app topType rhs)) b) extFvs sofar binFvs
        | _ =>
          mtrace on .zero with s!"[delab_simpStep preProcessed] At proof of type:\n{← ppExpr <| ← InferType proof l1 l2}\nAnd of value:\n{← ppExpr proof}\nExpected subproof ↓ to be a λ:\n{← ppExpr as[2]!}"
          return .none
      | ``have_unused_dep'  => do --have_unused_dep'
        let as := proof.getAppArgs
        match as[5]! with
        | .lam _ _ nx _ =>
          let .mk fv l1 l2 ← WithLocalDecl (`simpParse ++ (← mkFreshId)) as[0]! l1 l2
          let fv := .fvar fv
          let nx := nx.instantiate1 fv
          delab_simpStep l1 l2 preProcessed terminal nx topType extFvs sofar (binFvs.push fv)
        | _ =>
          mtrace on .zero with s!"[delab_simpStep preProcessed] At proof of type:\n{← ppExpr <| ← InferType proof l1 l2}\nAnd of value:\n{← ppExpr proof}\nExpected subproof ↓ to be a λ:\n{← ppExpr as[5]!}"
          return .none
      | ``have_unused' => do --have_unused'
        let as := proof.getAppArgs
        delab_simpStep l1 l2 preProcessed terminal as[5]! topType extFvs sofar binFvs
        -- beta's the topType
      | ``have_body_congr_dep' => do --have_body_congr_dep'
        let as := proof.getAppArgs
        match as[5]! with
        | .lam _ _ nx _ =>
          let .mk fv l1 l2 ← WithLocalDecl (`simpParse ++ (← mkFreshId)) as[0]! l1 l2
          let fv := .fvar fv
          let nx := nx.instantiate1 fv
          let a0 := Expr.abstract as[0]! binFvs
          let a2 := Expr.abstract as[2]! binFvs
          delab_simpStep l1 l2 preProcessed terminal nx (.lam `simpParse (.sort 0) (Expr.beta1Spe (.app topType (.app (.lam `simpParse a0 (.bvar (binFvs.size + 1)) .default) a2))) .default) extFvs sofar (binFvs.push fv)
          -- eta's the topType ; again in ↑ binder-type (.sort 0) is false and can't be made right, but its purpose is to be βed anyway
        | _ =>
          mtrace on .zero with s!"[delab_simpStep preProcessed] At proof of type:\n{← ppExpr <| ← InferType proof l1 l2}\nAnd of value:\n{← ppExpr proof}\nExpected subproof ↓ to be a λ:\n{← ppExpr as[5]!}"
          return .none
      | ``have_val_congr' => do -- have_val_congr'
        let as := proof.getAppArgs
        let a0 := Expr.abstract as[0]! binFvs
        let a4 := Expr.abstract as[4]! binFvs
        delab_simpStep l1 l2 preProcessed terminal as[5]!  (.lam `simpParse a0 (Expr.beta1Spe (.app topType (.lam `simpParse a4 (.bvar (binFvs.size + 1)) .default))) .default) extFvs sofar binFvs
      | ``have_body_congr' => do -- have_body_congr'
        let as := proof.getAppArgs
        match as[5]! with
        | .lam _ _ nx _ =>
          let .mk fv l1 l2 ← WithLocalDecl (`simpParse ++ (← mkFreshId)) as[0]! l1 l2
          let fv := .fvar fv
          let nx := nx.instantiate1 fv
          let a1 := Expr.abstract as[1]! binFvs
          let a0 := Expr.abstract as[0]! binFvs
          let a2 := Expr.abstract as[2]! binFvs
          delab_simpStep l1 l2 preProcessed terminal nx (.lam `simpParse a1 (Expr.beta1Spe (.app topType (.app (.lam `simpParse a0 (.bvar (binFvs.size + 1)) .default) a2))) .default) extFvs sofar (binFvs.push fv)
          -- eta's the topType ;
        | _ =>
          mtrace on .zero with s!"[delab_simpStep preProcessed] At proof of type:\n{← ppExpr <| ← InferType proof l1 l2}\nAnd of value:\n{← ppExpr proof}\nExpected subproof ↓ to be a λ:\n{← ppExpr as[5]!}"
          return .none
      | ``have_congr' => do -- have_body_congr'
        let as := proof.getAppArgs
        match as[7]! with
        | .lam _ _ nx _ =>
          let a0 := Expr.abstract as[0]! binFvs
          let a4 := Expr.abstract as[4]! binFvs
          let newTop : Expr := .lam `simpParse a0 (Expr.beta1Spe (.app topType (.app a4 (.bvar binFvs.size)))) .default
          let .some inter lif1 l1 l2 ← delab_simpStep l1 l2 preProcessed terminal as[6]! newTop extFvs sofar binFvs | return .none
          let a1 := Expr.abstract as[1]! binFvs
          let a3 := Expr.abstract as[3]! binFvs
          let newTop : Expr := (.lam `simpParse a1 (Expr.beta1Spe (.app topType (.app (.lam `simpParse a0 (.bvar (binFvs.size + 1)) .default) a3))) .default)
          let .mk fv l1 l2 ← WithLocalDecl (`simpParse ++ (← mkFreshId)) as[1]! l1 l2
          let fv := .fvar fv
          let nx := nx.instantiate1 fv
          let .some res lif2 l1 l2 ← delab_simpStep l1 l2 preProcessed terminal nx newTop extFvs inter (binFvs.push fv) | return .none
          return .some res (lif1 ++ lif2) l1 l2
        | _ =>
          mtrace on .zero with s!"[delab_simpStep preProcessed] At proof of type:\n{← ppExpr <| ← InferType proof l1 l2}\nAnd of value:\n{← ppExpr proof}\nExpected subproof ↓ to be a λ:\n{← ppExpr as[5]!}"
          return .none
      | ``Eq.refl => do --refl
        return .some sofar #[] l1 l2 -- only prior simp theorems matter
      | ``id => do -- strange simp_all case
        let nx := proof.getArg! 1
        match nx.getAppFn' with
        | .const n _ =>
          if n == ``Eq.mp
          then
            let extFvs := binFvs.foldl (fun x y => y.fvarId! :: x) extFvs
            let nx := nx.getArg! 2
            let .some res lif l1 l2 ← delab_simpStep l1 l2 preProcessed false nx (.lam `simpParse (.const `falseButOk []) (.bvar 0) .default) extFvs .nil #[] | return .none
            return .some sofar (lif.push res) l1 l2
          else
            return .none
        | _ => return .none
      | ``eq_false | ``eq_true =>
        let proof := consumeAndProjs (proof.getArg! 1)
        match proof.getAppFn' with
        | .const n _ =>
          if n == ``Eq.mp
          then
            let extFvs := binFvs.foldl (fun x y => y.fvarId! :: x) extFvs
            let nx := proof.getArg! 2
            let .some res lif l1 l2 ← delab_simpStep l1 l2 preProcessed true nx (.lam `simpParse (.const `falseButOk []) (.bvar 0) .default) extFvs .nil #[] | return .none
            return .some sofar (lif.push res) l1 l2
          else
            baseCase l1 l2 proof
        | _ => baseCase l1 l2 proof
      | _ =>
        baseCase l1 l2 proof
  | _ =>
      baseCase l1 l2 proof

-- #exit
#check have_congr'
#check Eq.refl

#check Expr.abstract
#check have_body_congr_dep'


partial def delab_simpGoal
  (l1 : LocalContext) (l2 : LocalInstances)
  (preProcessed : CTrie SimpCongrTheorem) (proof : Expr) (extFvs : List FVarId) (binFvs : Array Expr)
  : MetaM (OptionProd6 LocalContext LocalInstances (ListProd3 (List FVarId) Expr Expr) (Array (ListProd3 (List FVarId) Expr Expr)) (Array Expr) (Option Expr)) := do
  mtracing
  match proof.getAppFn' with
  | H@(.lam ..) => --revert
      let .mk p nfv l1 l2 ← LambdaLetTelescope H 0 l1 l2 -- with workers to disambiguate only
      let extFvs := nfv.foldl (fun x y => y.fvarId! :: x) extFvs
      mtrace on .one with s!" revert case with {← extFvs.mapM FVarId.getUserName}\np : {← ppExpr p}"
      let .some l1 l2 mainD iniL extL nonTerminal ← delab_simpGoal l1 l2 preProcessed p extFvs binFvs | return .none
      let mut sofar := iniL
      let mut extL := extL
      let as := proof.getAppArgs
      let mut L1 := l1
      let mut L2 := l2
      for a in as do
        match a.getAppFn' with
        | .const n _ => do
            if n == ``Eq.mp
            then
              let as := a.getAppArgs
              mtrace on .one with s!" expected, going on as2 {← ppExpr as[2]!}\nas3 : {← ppExpr as[3]!}"
              let .some inter lif1 l1 l2 ← delab_simpStep L1 L2 preProcessed false as[2]! (.lam `simpParse (.sort 0) (.bvar 0) .default) extFvs .nil binFvs | return .none
              -- as[2]! is expected to be a simpproof
              -- as[3]! can or not, be a simpproof (?)
              match ← delab_simpStep l1 l2 preProcessed false as[3]! (.lam `simpParse (.sort 0) (.bvar 0) .default) extFvs inter binFvs with
              | .none =>
                sofar := (sofar ++ lif1).push inter
                extL := extL.push as[3]!
                L1 := l1
                L2 := l2
              | .some inter lif2 l1 l2 =>
                sofar := (sofar ++ lif1 ++ lif2).push inter
                L1 := l1
                L2 := l2
            else
              -- unexpected
              mtrace on .zero with s!"[delab_simpGoal] expected an Eq.mp, got {← ppExpr a}"
              return .none
        | _ =>
          mtrace on .zero with s!"[delab_simpGoal] expected an Eq.mp, got {← ppExpr a}"
          return .none
      return .some L1 L2 mainD sofar extL nonTerminal
  | H@(.const h _) =>
      match h with
      | ``True.intro => -- trivial
          return .some l1 l2 (.cons extFvs (.const `True []) H .nil) #[] #[] .none
      | ``of_eq_true => -- terminal simp
          let p := proof.getArg! 1
          let .some f s l1 l2 ← delab_simpStep l1 l2 preProcessed true p (.lam `simpParse (.sort 0) (.bvar 0) .default) extFvs .nil binFvs | return .none
          return .some l1 l2 f s #[] .none
          -- simpproof of terminal simp (= True)
      | ``Eq.mpr => -- potentially non-terminal simp
          let as := proof.getAppArgs
          let eqP := as[2]!.getArg! 1 -- unwrap appli of `id`
          -- eqP is a simpproof
          match as[1]! with
          | .const n [] => do
              if n == ``False
              then
                mtrace on .zero with s!" expeted case for head {h}, going on \nas3 {← ppExpr as[3]!}\neqP {← ppExpr eqP}"
                let inter ← delab_simpGoal l1 l2 preProcessed as[3]! extFvs binFvs
                match inter with
                | .none => -- as[3]! could be a non-simp-proof, apparently
                  let .some lres lif2 l1 l2 ← delab_simpStep l1 l2 preProcessed true eqP (.lam `simpParse (.sort 0) (.bvar 0) .default) extFvs .nil binFvs | return .none
                  return .some l1 l2 .nil (lif2.push lres) (#[as[3]!]) .none
                | .some l1 l2 mainD lif1 extL nonTerminal =>
                  -- because we expect it to be a `False.elim`
                  -- couldn't read this off of `simpGoal`, but appears in `ConvexCone.salient_positive`
                  let .some lres lif2 l1 l2 ← delab_simpStep l1 l2 preProcessed true eqP (.lam `simpParse (.sort 0) (.bvar 0) .default) extFvs .nil binFvs | return .none
                  return .some l1 l2 mainD ((lif1 ++ lif2).push lres) extL nonTerminal
              else
                -- here we only expect `eqP` to be a simpproof of a non-terminal simp (ie. no = True or = False)
                let .some f s l1 l2 ← delab_simpStep l1 l2 preProcessed true eqP (.lam `simpParse (.sort 0) (.bvar 0) .default) extFvs .nil binFvs | return .none
                return .some l1 l2 f s #[] (.some as[3]!)
          | _ =>
            -- here we only expect `eqP` to be a simpproof of a non-terminal simp (ie. no = True or = False)
            let .some f s l1 l2 ←  delab_simpStep l1 l2 preProcessed true eqP (.lam `simpParse (.sort 0) (.bvar 0) .default) extFvs .nil binFvs | return .none
            return .some l1 l2 f s #[] (.some as[3]!)
      | ``False.elim =>
          let H := (proof.getArg! 1)
          match H.getAppFn' with
          | .const n _ => do
              if n == ``Eq.mp
              then
                let as := H.getAppArgs
                mtrace on .one with s!" expected, going on as2 {← ppExpr as[2]!}\nas3 : {← ppExpr as[3]!}"
                let .some mainD lif1 l1 l2 ← delab_simpStep l1 l2 preProcessed true as[2]! (.lam `simpParse (.sort 0) (.bvar 0) .default) extFvs .nil binFvs | return .none
                -- as[2]! is expected to be a simpproof of ( = False)
                -- as[3]! can or not, be a simpproof (?)
                match ← delab_simpStep l1 l2 preProcessed false as[3]! (.lam `simpParse (.sort 0) (.bvar 0) .default) extFvs .nil binFvs with
                | .none =>
                  return .some l1 l2 mainD lif1 #[as[3]!] .none
                | .some lres lif2 l1 l2 =>
                  return .some l1 l2 mainD ((lif1 ++ lif2).push lres) #[] .none
              else
                -- can apparently be a non-simpproof ??
                return .none
          | _ =>
            -- can apparently be a non-simpproof ??
            return .none
      | ``id => -- couldn't read this from simp, but appears in terms ; may come from revert-ish step ?
          let a := (proof.getArg! 1)
          match a.getAppFn' with
          | .const n _ => do
              if n == ``Eq.mp
              then
                let as := a.getAppArgs
                mtrace on .one with s!" expected, going on as2 {← ppExpr as[2]!}\nas3 : {← ppExpr as[3]!}"
                let .some inter lif1 l1 l2 ← delab_simpStep l1 l2 preProcessed false as[2]! (.lam `simpParse (.sort 0) (.bvar 0) .default) extFvs .nil binFvs | return .none
                -- as[2]! is expected to be a simpproof
                -- as[3]! can or not, be a simpproof (?)
                match ← delab_simpStep l1 l2 preProcessed false as[3]! (.lam `simpParse (.sort 0) (.bvar 0) .default) extFvs inter binFvs with
                | .none =>
                  let sofar := lif1.push inter
                  let extL := #[as[3]!]
                  return .some l1 l2 .nil sofar extL .none
                | .some inter lif2 l1 l2 =>
                  let sofar := (lif1 ++ lif2).push inter
                  return .some l1 l2 .nil sofar #[] .none
              else
                -- can happen ... in `List.reverse_cons` for example
                mtrace on .zero with s!" expected an Eq.mp, got {← ppExpr a}"
                return .some l1 l2 .nil #[] #[] <| .some a
          | _ =>
            mtrace on .zero with s!" expected an Eq.mp, got {← ppExpr a}"
            return .none
      | _ => -- not simp
          return .none
  | _ => -- not simp
     return .none


#check 1

def mkPreProCongr : CoreM (CTrie SimpCongrTheorem) := do
  let thms ← Meta.getSimpCongrTheorems
  let mut out := CTrie.empty
  for (_,vals) in thms.lemmas do
    for val in vals do
      out := out.insert val.theoremName.toString.toUTF8 val
  return out


#check 1


def cleanBetaTopTypes (res : ListProd3 (List FVarId) Expr Expr) :  ListProd3 (List FVarId) Expr Expr :=
  res.foldl .nil (fun x y z R =>
    let y := y.onAllSubtermsTR (fun
      | .app (.lam _ _ b _) v => b.instantiate1 v
      | x => x
      )
    .cons x y z R
    )

def cleanBetaTopType (res : Expr) : Expr :=
    res.onAllSubtermsTR (fun
      | .app (.lam _ _ b _) v => b.instantiate1 v
      | x => x
      )


#check 1

partial def simpProof_topDelab (res : ListProd3 (List FVarId) Expr Expr)
  : MetaM (OptionProd (List FVarId) Name) := do
  mtracing
  match res with
  | .nil => return .none
  | .cons lif _ proof _ =>
    let rec main (proof : Expr) : MetaM (OptionProd (List FVarId) Name) :=
      match proof.getAppFn' with
      | .const n _ =>
        match n with
        | ``Eq.symm =>
          match (proof.getArg! 3).getAppFn' with
          | .const n _ => return .some lif n
          | _ => return .none
        | ``propext =>
          match (proof.getArg! 2).getAppFn' with
          | .const n _ => return .some lif n
          | _ => return .none
        | ``eq_true | ``eq_false | ``Bool.of_not_eq_true | ``Bool.of_not_eq_false =>
          match (proof.getArg! 1).getAppFn' with
          | .const n _ => return .some lif n
          | _ => return .none
        | _ =>
          match n with
          | .str _ suf => do
            if String.isPrefixOf "_simp" suf
            then
              let .some info := (← getEnv).find? n | throwError s!"[simpProof_topDelab] {n} not in env ??"
              let sub := info.value!
              lambdaLetTelescope sub <| fun _ sub => do
                main sub
            else
              return .some lif n
          | _ =>
            return .some lif n
      | .proj _ _ e =>
        main e
      | _ => return .none
    main proof


#check 1


partial def simpProof_topDelab' (res : ListProd3 (List FVarId) Expr Expr)
  : MetaM (OptionProd3 (List FVarId) Expr Name) :=
  match res with
  | .nil => return .none
  | .cons lif T proof _ =>
    let rec main (proof : Expr) : MetaM (OptionProd3 (List FVarId) Expr Name) :=
      match proof.getAppFn' with
      | .const n _ =>
        match n with
        | ``Eq.symm =>
          match (proof.getArg! 3).getAppFn' with
          | .const n _ => return .some lif T n
          | _ => return .none
        | ``propext =>
          match (proof.getArg! 2).getAppFn' with
          | .const n _ => return .some lif T n
          | _ => return .none
        | ``eq_true | ``eq_false | ``Bool.of_not_eq_true | ``Bool.of_not_eq_false =>
          match (proof.getArg! 1).getAppFn' with
          | .const n _ => return .some lif T n
          | _ => return .none
        | _ =>
          match n with
          | .str _ suf => do
            if String.isPrefixOf "_simp" suf
            then
              let .some info := (← getEnv).find? n | throwError s!"[simpProof_topDelab] {n} not in env ??"
              let sub := info.value!
              lambdaLetTelescope sub <| fun _ sub => do
                main sub
            else
              return .some lif T n
          | _ =>
            return .some lif T n
      | .proj _ _ e =>
        main e
      | _ => return .none
    main proof


#check 1

partial def simpProof_topDelab_forTest (proof : Expr) : MetaM (Option Name) :=
  match proof.getAppFn' with
  | .const n _ =>
    match n with
    | ``Eq.symm =>
      match (proof.getArg! 3).getAppFn' with
      | .const n _ => return .some n
      | _ => return .none
    | ``propext =>
      match (proof.getArg! 2).getAppFn' with
      | .const n _ => return .some n
      | _ => return .none
    | ``eq_true | ``eq_false | ``Bool.of_not_eq_true | ``Bool.of_not_eq_false =>
      match (proof.getArg! 1).getAppFn' with
      | .const n _ => return .some n
      | _ => return .none
    | _ =>
      match n with
      | .str _ suf => do
        if String.isPrefixOf "_simp" suf
        then
          let .some info := (← getEnv).find? n | throwError s!"[simpProof_topDelab] {n} not in env ??"
          let sub := info.value!
          lambdaLetTelescope sub <| fun _ sub => do
            simpProof_topDelab_forTest sub
        else
          return .some n
      | _ =>
        return .some n
  | .proj _ _ e =>
    simpProof_topDelab_forTest e
  | _ => return .none
