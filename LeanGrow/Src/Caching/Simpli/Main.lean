

/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Caching.Formating.Types
import LeanGrow.Src.Data.CTrie.Basic


open Lean Meta


def ThmFormat.pathologicalMvarApp? : ThmFormat → Bool
  | .std _ _ _ _ _ _ goal .. | .rw _ _ _ goal .. =>
    match goal.getAppFn with
    | .mvar .. => goal.getAppArgs.all (fun | .mvar .. => true | _ => false)
    | _ => false

-- ↑ to avoid ↓
#check if_pos
#check congr

-- use ↓ instead ?? should be bad for back
def actualPatho (e : Expr) : Bool :=
  e.onAllSubtermsCheckExists (fun
    | x@(.app ..) =>
        match x.getAppFn with
        | .mvar .. => x.getAppArgs.all (fun | .mvar .. => true | _ => false)
        | _ => false
    | _ => false)



/-- Important wrt `getAtomsWithMulti` : expects a strict order ! -/
def List.orderedInsertOrLeaveS {α : Type _} [BEq α] (r : α → α → Bool) (a : α) : List α → List α
  | [] => [a]
  | b :: l => if r a b then a :: b :: l else (if a == b then b :: l else b :: List.orderedInsertOrLeaveS r a l)

@[specialize, inline]
partial def Lean.Expr.onAllSubtermsFoldSkipM_alt (e : Expr) (initD : LocalContext) (initI : LocalInstances)
  {α : Sort _} (initA : α)
  (f : Expr → Nat → CTrie Unit → LocalContext → LocalInstances → α → MetaM (Prod4 Bool α LocalContext LocalInstances))
  : MetaM (Prod3 α LocalContext LocalInstances) :=
  let rec @[specialize] go (workas : CTrie Unit) (initD : LocalContext) (initI : LocalInstances) (col : α)
    : ListProd Nat Expr → MetaM (Prod3 α LocalContext LocalInstances)
    | .nil => return ⟨col,initD,initI⟩
    | .cons d e more => do
      let ⟨skip?,col,initD,initI⟩  ← f e d workas initD initI col
      if skip?
      then
        go workas initD initI col more
      else
        match e with
        | .app l r => go workas initD initI col (.cons d l <| .cons d r more)
        | .lam _ l r _ =>
            let fv ← worker d
            let workas := workas.insert fv.toString.toUTF8 ()
            let ⟨_,r,initD,initI⟩ ← withFreeing fv l r initD initI
            go workas initD initI col (.cons d l <| .cons (d+1) r more)
        | .forallE _ l r _ =>
            let fv ← worker d
            let workas := workas.insert fv.toString.toUTF8 ()
            let ⟨_,r,initD,initI⟩ ← withFreeing fv l r initD initI
            go workas initD initI col (.cons d l <| .cons (d+1) r more)
        | .letE _ l r z _ =>
            let fv ← worker d
            let workas := workas.insert fv.toString.toUTF8 ()
            let ⟨_,z,initD,initI⟩ ← withFreeingLet fv l r z initD initI
            go workas initD initI col (.cons d l <| .cons d r <| .cons (d+1) z more)
        | .proj _ _ e => go workas initD initI col (.cons d e more)
        | .mdata _ e => go workas initD initI col (.cons d e more)
        | _ => go workas initD initI col more
  go {} initD initI initA <| .cons 0 e .nil



def Lean.Expr.getAtomsWithMulti
  (l1 : LocalContext) (l2 : LocalInstances)
  (e : Expr) : MetaM (Prod3 (Nat × List Expr) LocalContext LocalInstances)  :=
  e.onAllSubtermsFoldSkipM l1 l2 (0,[]) (fun s _ _ l1 l2 (c,as) => do
    if ← IsProof s l1 l2 -- ignore instances too ?
    then
      return .mk (c,as) true l1 l2
    else
      match s with
      | .const .. | .fvar _ | .mvar _ | .lit _ | .sort _ | .bvar _ =>
          return .mk (c+1, as.orderedInsertOrLeaveS Expr.lt s) false l1 l2
      | _ => return .mk (c,as) false l1 l2
    )

-- #exit

def List.orderedContainsS {α : Type _} [BEq α] (r : α → α → Bool)  (a : α) : List α → Bool
| [] => false
| x :: l => if r x a then (List.orderedContainsS r a l) else (x == a)


/--
**TODO** : is symetric, so do the fixes to run it once per rw to tell which is the simplifier, if any

- Easy examples: → for `if_pos` and `Nat.add_zero`
- To allow → of `dif_pos`, we ignore inclusion of mvars (hyps)
- Ignoring mvars also handles polymorphism "issues", as in `List.length_map`
- We count atoms with multiplicity to allow → of `List.dedup_idem`, but prohibit `Nat.add_comm`
-/
def isSimplifierCore (l1 : LocalContext) (l2 : LocalInstances)
  (init new : Expr) : MetaM (Prod3 Bool LocalContext LocalInstances) := do
    if init != new
    then
      let .mk (ic,ia) l1 l2 ← init.getAtomsWithMulti l1 l2
      let .mk (nc,na) l1 l2 ← new.getAtomsWithMulti l1 l2
      dbg_trace s!"ic : {ic}"
      dbg_trace s!"ia : {ia}"
      dbg_trace s!"nc : {nc}"
      dbg_trace s!"na : {na}"
      if nc ≥ ic
      then
        return .mk false l1 l2
      else
        return .mk (na.all (fun | .mvar _ => true | x => ia.orderedContainsS Expr.lt x)) l1 l2
        -- optimize : make fold that doesn't pick up mvars anyway
    else
      return .mk false l1 l2

-- #exit

#check if_pos
#check dif_pos
#check_failure List.dedup_idem
#check Nat.add_zero
#check Nat.add_comm

#check List.getElem_map
#check List.length_map

def isSimplifierFuzzCore (l1 : LocalContext) (l2 : LocalInstances)
  (init new : Expr) (ratio : Float) : MetaM (Prod3 Bool LocalContext LocalInstances) := do
    if init != new
    then
      let .mk (ic,ia) l1 l2 ← init.getAtomsWithMulti l1 l2
      let .mk (nc,na) l1 l2 ← new.getAtomsWithMulti l1 l2
      if nc ≥ ic
      then
        return .mk false l1 l2
      else
        let ina := na.foldl (fun S x => if ia.orderedContainsS Expr.lt x then S+1 else S) 0
        if ina.toFloat / na.length.toFloat ≥ ratio
        then return .mk true l1 l2
        else return .mk false l1 l2
        -- optimize : make fold that doesn't pick up mvars anyway
    else
      return .mk false l1 l2


-- Simplifier under if/dif or ∨

#check Nat.le_or_eq_of_le_succ
#check Nat.lt_or_gt_of_ne
#check Nat.ne_iff_lt_or_gt

@[specialize]
partial def isSimplifierCondSpe
  (core : LocalContext → LocalInstances → Expr → Expr → MetaM (Prod3 Bool LocalContext LocalInstances))
  (l1 : LocalContext) (l2 : LocalInstances)
  (init new : Expr) : MetaM (Prod3 Bool LocalContext LocalInstances) := do
  let r@(.mk fst l1 l2) ← core l1 l2 init new
  if fst
  then return r
  else
    match new.getAppFn' with
    | .const h _ =>
        if h == ``ite
        then
          let as := new.getAppArgs
          let .mk b l1 l2 ← isSimplifierCondSpe core l1 l2 init as[3]!
          if b
          then isSimplifierCondSpe core l1 l2 init as[4]!
          else return .mk false l1 l2
        else
          if h == ``dite
          then
            let as := new.getAppArgs
            let A ← InferType as[3]! l1 l2
            let mv ← mkFreshExprMVar (.some A.bindingDomain!)
            let .mk b l1 l2 ← isSimplifierCondSpe core l1 l2 init (A.bindingBody!.instantiate1 mv)
            if b
            then
              let A ← InferType as[4]! l1 l2
              let mv ← mkFreshExprMVar (.some A.bindingDomain!)
              isSimplifierCondSpe core l1 l2 init (A.bindingBody!.instantiate1 mv)
            else
              return .mk false l1 l2
          else
            if h == ``Or
            then
              let as := new.getAppArgs
              let .mk b l1 l2 ← isSimplifierCondSpe core l1 l2 init as[0]!
              if b
              then isSimplifierCondSpe core l1 l2 init as[1]!
              else return .mk false l1 l2
            else
              return .mk false l1 l2
    | _ => return .mk false l1 l2


def isSimplifierCond := isSimplifierCondSpe isSimplifierCore

def isSimplifierCondFuzz (ratio : Float) := isSimplifierCondSpe (isSimplifierFuzzCore · · · · ratio)



#check Int.le_add_one

def MCtxData.dup (mc : MCtxData) : MCtxData where
  lDepth := mc.lDepth.map (fun (⟨l⟩,d) => (⟨.str l "dup"⟩,d))
  decls := mc.decls.map (fun (⟨l⟩,d) =>
      let d := {d with userName := .str d.userName "dup", type := d.type.onAllSubtermsTR (fun | .mvar ⟨m⟩ => .mvar ⟨.str m "dup"⟩ | x => x)}
      (⟨.str l "dup"⟩,d))
  userNames := mc.userNames.map (fun (d,⟨l⟩) => (.str d "dup",⟨.str l "dup"⟩))


/-- Assumes mvars to be loaded-/
def isBadForForw (sinks : List Nat) (hyps : Array HypType) (goal : Expr) (mc : MCtxData) : MetaM Bool := do
  match sinks with
  | [sing] =>
      let mcd := mc.dup
      mcd.load
      let goal := goal.onAllSubtermsTR (fun | .mvar ⟨m⟩ => .mvar ⟨.str m "dup"⟩ | x => x)
      let S := hyps[sing]!.type
      fullApproxDefEq <| isDefEqGuarded goal S
  | _ => return false


-- consider eq_i and simps theorems as simplifiers by default, going from left to right only ?


def eqSyntacticUpToMVar (eWiMv eNoMv : Expr) : Bool :=
  match eWiMv, eNoMv with
  | .app x y, .app u v | .lam _ x y _, .lam _ u v _ | .forallE _ x y _, .forallE _ u v _ =>
    (eqSyntacticUpToMVar x u) && (eqSyntacticUpToMVar y v)
  | .letE _ x y z _, .letE _ u v w _ => (eqSyntacticUpToMVar x u) && (eqSyntacticUpToMVar y v) && (eqSyntacticUpToMVar z w)
  | .proj n i x, .proj m j u => n == m && i == j && (eqSyntacticUpToMVar x u)
  | .mdata _ x, .mdata _ u => (eqSyntacticUpToMVar x u)
  | .mvar _, _ => true
  | .sort x, .sort u => Level.EqUpToMVar x u
  | .const n x, .const m u => n == m && (List.zipWith Level.EqUpToMVar x u).all (· == true)
  | _, _ => eWiMv == eNoMv

#check Level.EqUpToMVar



-- Thought dump : dissallow Eq.trans as backsteps from grow ? via some sort of heristic ?
-- Maybe any sink hyps unify with goal ? Try ↓
def isBadForBack
  (module : Name) (thmIdx : Nat)
  (sinks : List Nat) (hyps : Array HypType) (goal : Expr)  : MetaM Bool := do
  match sinks with
  | _ :: _ =>
      let mut l1 ← getLCtx
      let mut l2 ← getLocalInstances
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
      withLCtx l1 l2 <| do
        dbg_trace s!"[isBadForBack] {← ppExpr goal}"
        for sink in sinks do
          let S := hyps[sink]!.type.onAllSubtermsTR (fun
            | .mvar ⟨m⟩ => .fvar ⟨m⟩
            | .sort u => .sort (u.onAllSubterms (fun | .mvar id => .param id.name | x => x))
            | .const n us => .const n (us.map (fun u => (u.onAllSubterms (fun | .mvar id => .param id.name | x => x))))
            | x => x)
          dbg_trace s!"[isBadForBack] {← ppExpr S}"
          if eqSyntacticUpToMVar goal S
          then
            return true
          else
            if ← fullApproxDefEq <| isDefEqGuarded goal S
            then
              return true
            else
              clearMvarAssignments
              continue
        return false
  | _ => return false

-- TODO: test


def isBadForBackRW
  (module : Name) (thmIdx : Nat)
  (sinks : List Nat) (hyps : Array HypType) (ini rep : Expr)  : MetaM Bool := do
  let sinks := hyps.size :: sinks -- was it sorted ??
  let hyps := hyps.push (.reg rep)
  isBadForBack module thmIdx sinks hyps ini
  -- ini shouldn't be a pattern of of any of the sinks ? or any of the hyps actually
  -- ini shouldn't be a pattern of rep
  -- here we only check exact match not subpattern match ...


/-
3 categories:
- Pathological:
  Should not be included as a theorem for grow. For example, contained mvar apps,
  since they cause bad unification behaviour
- Bad (forw or back):
  Keep them, but give lower score ? Meant for thms that would be applicable to the
  results of their applicaion, thereby displaying looping behaviour
- Simplifier:
  For rws: if the replacement is a simplification of the original. Maybe return
  factor instead of deciding via ratio, and use factor toscore ?

-/


#check List.map_cons
-- contains mvar app in the form of `f a`
