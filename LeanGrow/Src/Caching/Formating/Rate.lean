
/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Utils.Lean.MetaAPI
import LeanGrow.Src.Caching.Formating.Types


open Lean Meta

@[inline]
def Lean.Expr.isMvarApp (goal : Expr) : Bool :=
  match goal.getAppFn' with
  | .mvar .. => goal.getAppArgs.all (fun | .mvar .. => true | _ => false)
  | _ => false

def ListProd.incKeyBy {α : Type _} [BEq α] (r : α → α → Bool) (a : α) (v : Nat)
  : ListProd Nat α → ListProd Nat α
  | .nil => .cons v a .nil
  | .cons w b l => if r a b then .cons v a (.cons w b l) else (if a == b then .cons (w + v) b l else .cons w b (l.incKeyBy r a v))

def ListProd.findVal {α : Type _} [BEq α] (r : α → α → Bool)  (a : α) : ListProd Nat α → Option Nat
| .nil => .none
| .cons v x l => if r x a then (l.findVal r a) else (if x == a then v else .none)

@[inline]
def Lean.Expr.getAtomsWithMultiIgnoringMvarAndConstLevels
  (l1 : LocalContext) (l2 : LocalInstances)
  (e : Expr) : MetaM (Prod3 (Nat × ListProd Nat Expr) LocalContext LocalInstances)  :=
  e.onAllSubtermsFoldSkipM l1 l2 (0,.nil) (fun s depth _ l1 l2 (c,as) => do
    if ← IsProof s l1 l2
    then
      return .mk (c,as) true l1 l2
    else
      let T ← InferType s l1 l2
      match ← IsClass? T l1 l2 with
      | .some .. =>
        return .mk (c,as) true l1 l2
      | _ =>
        match s with
        | .lit _ | .sort _ | .bvar _ =>
            return .mk (c+1, as.incKeyBy Expr.lt s 1) false l1 l2
        | .const n _ =>
            let s := Expr.const n []
            return .mk (c+1, as.incKeyBy Expr.lt s 1) false l1 l2
        | .fvar fvid =>
            match fvid.name with
            | .num (.str _ k) ld =>
              if k == "w"
              then
                let s := Expr.bvar (depth - (ld+1))
                return .mk (c+1, as.incKeyBy Expr.lt s 1) false l1 l2
              else
                return .mk (c+1, as.incKeyBy Expr.lt s 1) false l1 l2
            | _ =>
              return .mk (c+1, as.incKeyBy Expr.lt s 1) false l1 l2
        | _ => return .mk (c,as) false l1 l2
    )


/-- Is in [0,1]-/
@[inline]
def simplifierScoreCore (l1 : LocalContext) (l2 : LocalInstances)
  (init new : Expr) : MetaM (Prod3 Float LocalContext LocalInstances) := do
    mtracing
    if init != new
    then
      let .mk (ic,ia) l1 l2 ← init.getAtomsWithMultiIgnoringMvarAndConstLevels l1 l2
      let .mk (nc,na) l1 l2 ← new.getAtomsWithMultiIgnoringMvarAndConstLevels l1 l2
      mtrace on .zero with s!"ic {ic} nc {nc}\nia: {ia}\nna: {na}" -- atoms so repr is fine
      if nc ≤ ic
      then
        let (top,bot) := na.foldl (0,0) (fun mul a (top,bot) =>
          match ia.findVal Expr.lt a with
          | .some v =>
              if mul < v
              then (top + (v - mul), bot + (v - mul))
              else (top, bot + (mul - v))
          | _ => (top, bot + mul)
          )
        mtrace on .zero with s!" top {top} bot {bot}"
        if bot == 0
        then -- same number of shared atoms, and all new are included in initial
          return .mk (if nc == ic then 0.5 else 1) l1 l2
        else
          let score := top.toFloat / bot.toFloat
          return .mk score l1 l2
      else
        return .mk 0 l1 l2
    else
      return .mk 0 l1 l2


@[inline]
partial def simplifierScore
  (l1 : LocalContext) (l2 : LocalInstances)
  (init new : Expr) : MetaM (Prod3 Float LocalContext LocalInstances) := do
  mtracing
  let avg (x y : Float) := (x + y) / 2
  mtrace on .zero with s!" on new {← PpExpr new l1 l2}"
  let .mk fst l1 l2 ← simplifierScoreCore l1 l2 init new
  mtrace on .zero with s!" fst {fst}"
  match new.getAppFn' with
  | .const h _ =>
      if h == ``ite
      then
        let as := new.getAppArgs
        let .mk l l1 l2 ← simplifierScore l1 l2 init as[3]!
        let .mk r l1 l2 ← simplifierScore l1 l2 init as[4]!
        mtrace on .zero with s!" l {l} r {r}"
        return .mk (max fst (avg l r)) l1 l2
      else
        if h == ``dite
        then
          let as := new.getAppArgs
          let l ← (do
            match as[3]! with
            | .lam _ t b _ =>
              let mv ← mkFreshExprMVar t
              return b.instantiate1 mv
            | x => return x)
          let .mk l l1 l2 ← simplifierScore l1 l2 init l
          let r ← (do
            match as[4]! with
            | .lam _ t b _ =>
              let mv ← mkFreshExprMVar t
              return b.instantiate1 mv
            | x => return x)
          let .mk r l1 l2 ← simplifierScore l1 l2 init r
          mtrace on .zero with s!" l {l} r {r}"
          return .mk (max fst (avg l r)) l1 l2
        else
          if h == ``Or
          then
            let as := new.getAppArgs
            let .mk l l1 l2 ← simplifierScore l1 l2 init as[0]!
            let .mk r l1 l2 ← simplifierScore l1 l2 init as[1]!
            mtrace on .zero with s!" l {l} r {r}"
            return .mk (max fst (avg l r)) l1 l2
          else
            if h == ``And
            then
              let as := new.getAppArgs
              let .mk l l1 l2 ← simplifierScore l1 l2 init as[0]!
              let .mk r l1 l2 ← simplifierScore l1 l2 init as[1]!
              mtrace on .zero with s!" l {l} r {r}"
              return .mk (max fst (avg l r)) l1 l2
            else
              return .mk fst l1 l2
  | _ => return .mk fst l1 l2


@[inline]
def isBadForRW (l1 : LocalContext) (l2 : LocalInstances) (init rep : Expr) : MetaM Bool := do
  mtracing
  let Rep ← Whnf rep l1 l2
  mtrace on .zero with s!"\nrep from: {← PpExpr rep l1 l2}\nrep to: {← PpExpr Rep l1 l2}"
  -- let Init ← withTransparency .instances <| withLCtx l1 l2 <| reduce init
  mtrace on .zero with s!"\ninit from: {← PpExpr init l1 l2}"
  return init == Rep

@[inline]
def isGoodForRW (l1 : LocalContext) (l2 : LocalInstances) (init rep : Expr) : MetaM Bool := do
  mtracing
  let Init ← Whnf init l1 l2
  mtrace on .zero with s!"\ninit from: {← PpExpr init l1 l2}\nrep to: {← PpExpr Init l1 l2}"
  -- let Rep ← withTransparency .instances <| withLCtx l1 l2 <| reduce rep
  mtrace on .zero with s!"\nrep from: {← PpExpr rep l1 l2}"
  return Init == rep



@[inline]
def badnessTestPrep (l1 : LocalContext) (l2 : LocalInstances)
  (module : Name) (thmIdx : Nat) (hyps : Array HypType)
  : MetaM (Prod LocalContext LocalInstances) := do
  let mut l1 := l1
  let mut l2 := l2
  let mut i := 0
  for h in hyps do
    let fvn := lnode module thmIdx i
    let T := h.type.onAllSubtermsTR (fun
      | .mvar ⟨m⟩ => .fvar ⟨m⟩
      | .sort u => .sort (u.onAllSubterms (fun | .mvar id => .param id.name | x => x))
      | .const n us => .const n (us.map (fun u => (u.onAllSubterms (fun | .mvar id => .param id.name | x => x))))
      | x => x)
    let .mk _ l1' l2' ← WithLocalDecl fvn T l1 l2
    l1 := l1'
    l2 := l2'
    i := i+1
  i := 0
  for _ in hyps do
    let fvn := MVarId.mk <| lnode module thmIdx i
    fvn.modifyDecl (fun c => {c with lctx := l1, localInstances := l2})
    i := i+1
  return (l1,l2)


@[inline]
def isBadForForw (l1 : LocalContext) (l2 : LocalInstances)
  (sinks : List Nat) (hyps : Array HypType) (goal : Expr) : MetaM Bool := do
  match sinks with
  | [sing] =>
      let goal := goal.onAllSubtermsTR (fun
        | .mvar ⟨m⟩ => .fvar ⟨m⟩
        | .sort u => .sort (u.onAllSubterms (fun | .mvar id => .param id.name | x => x))
        | .const n us => .const n (us.map (fun u => (u.onAllSubterms (fun | .mvar id => .param id.name | x => x))))
        | x => x)
      let S := hyps[sing]!.type
      let r ← withTransparency .instances <| defEqWiMv goal S l1 l2
      return r.isSome
  | _ => return false


@[inline]
def isBadForForwRW (l1 : LocalContext) (l2 : LocalInstances) (init rep : Expr)
  : MetaM (Prod3 Bool LocalContext LocalInstances) := do
    mtracing
    if ← isBadForRW l1 l2 init rep
    then
      mtrace on .zero with s!" decisively bad from isBadForRW"
      return .mk true l1 l2
    else
      if ← isGoodForRW l1 l2 init rep
      then
        mtrace on .zero with s!" decisively not bad from isGoodForRW"
        return .mk false l1 l2
      else
        let rep := rep.onAllSubtermsTR (fun
          | .mvar ⟨m⟩ => .fvar ⟨m⟩
          | .sort u => .sort (u.onAllSubterms (fun | .mvar id => .param id.name | x => x))
          | .const n us => .const n (us.map (fun u => (u.onAllSubterms (fun | .mvar id => .param id.name | x => x))))
          | x => x)
        rep.onAllSubtermsCheckExistsM l1 l2 (fun g _ l1 l2 => do
          let r ← withTransparency .instances <| defEqWiMv init g l1 l2
          return .mk r.isSome l1 l2
          )


@[inline]
def isBadForBack (l1 : LocalContext) (l2 : LocalInstances)
  (sinks : List Nat) (hyps : Array HypType) (goal : Expr) : MetaM Bool := do
    for sink in sinks do
      let S := hyps[sink]!.type.onAllSubtermsTR (fun
        | .mvar ⟨m⟩ => .fvar ⟨m⟩
        | .sort u => .sort (u.onAllSubterms (fun | .mvar id => .param id.name | x => x))
        | .const n us => .const n (us.map (fun u => (u.onAllSubterms (fun | .mvar id => .param id.name | x => x))))
        | x => x)
      let r ← withTransparency .instances <| defEqWiMv goal S l1 l2
      match r with
      | .some .. => return true
      | _ => continue
    return false


@[inline]
def isBadForBackRW (l1 : LocalContext) (l2 : LocalInstances)
  (sinks : List Nat) (hyps : Array HypType) (init rep : Expr)
  : MetaM (Prod3 Bool LocalContext LocalInstances) := do
    mtracing
    if ← isBadForRW l1 l2 init rep
    then
      mtrace on .zero with s!" decisively bad from isBadForRW"
      return .mk true l1 l2
    else
      if ← isGoodForRW l1 l2 init rep
      then
        mtrace on .zero with s!" decisively not bad from isGoodForRW"
        return .mk false l1 l2
      else
        let rep := rep.onAllSubtermsTR (fun
          | .mvar ⟨m⟩ => .fvar ⟨m⟩
          | .sort u => .sort (u.onAllSubterms (fun | .mvar id => .param id.name | x => x))
          | .const n us => .const n (us.map (fun u => (u.onAllSubterms (fun | .mvar id => .param id.name | x => x))))
          | x => x)
        let R@(.mk res l1 l2) ← rep.onAllSubtermsCheckExistsM l1 l2 (fun g _ l1 l2 => do
          let r ← withTransparency .instances <| defEqWiMv init g l1 l2
          return .mk r.isSome l1 l2
          )
        if res
        then
          mtrace on .zero with s!" bad from replacement uni"
          return R
        else
          let mut l1 := l1
          let mut l2 := l2
          for sink in sinks do
            let S := hyps[sink]!.type.onAllSubtermsTR (fun
              | .mvar ⟨m⟩ => .fvar ⟨m⟩
              | .sort u => .sort (u.onAllSubterms (fun | .mvar id => .param id.name | x => x))
              | .const n us => .const n (us.map (fun u => (u.onAllSubterms (fun | .mvar id => .param id.name | x => x))))
              | x => x)
            let R@(.mk r l1' l2') ← S.onAllSubtermsCheckExistsM l1 l2 (fun g _ l1 l2 => do
              let r ← withTransparency .instances <| defEqWiMv init g l1 l2
              return .mk r.isSome l1 l2
              )
            l1 := l1'
            l2 := l2'
            mtrace on .zero with s!" test result {r} on sink {← PpExpr S l1 l2}"
            if r
            then return R
            else continue
          return .mk false l1 l2
