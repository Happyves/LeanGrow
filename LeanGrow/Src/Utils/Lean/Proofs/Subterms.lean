
/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Utils.Lean.Expr.Basic
import Lean

open Lean Meta


def mkValLikeCore (n : Name) : MetaM Unit := do
  let env ← getEnv
  let .some info := (env.find? n) | throwError s!"{n} unknown"
  let .some val := info.value? | throwError s!"{n} has no value"
  let N := Name.str n "like"
  let eq ← mkEq (.const n (info.levelParams.map .param)) val
  let dec : Declaration := .defnDecl <| {
    name := N
    levelParams := info.levelParams
    type := .sort 0
    value := eq
    hints := .regular 0
    safety := .safe
  }
  addDecl dec

-- elab "add_valLike" n:ident : command => do
--   let N := n.getId
--   Elab.Command.liftTermElabM (mkValLikeCore N)

elab "ppElabOf" t:term : term => do
  let t ← Elab.Term.elabTermAndSynthesize t .none
  logInfoAt (← getRef) ( t)
  return t

#check 1

open Elab Term


def help : Expr → TermElabM FVarId
  | .mdata _ e => help e
  | .fvar i => return i
  | _ => throwError "bad format"


@[inline]
partial def Lean.Expr.abstractLetFvarLam'
  (initD : LocalContext) (initI : LocalInstances)
  (fvs : Array FVarId) (e : Expr)
  : MetaM (Prod3 Expr LocalContext LocalInstances) :=
    let rec bind (term : Expr) (i : Nat) (initD : LocalContext) (initI : LocalInstances) : MetaM (Prod3 Expr LocalContext LocalInstances) := do
     dbg_trace s!"bind {repr (fvs[i]!)}"
      match ← (fvs[i]!).GetDecl initD initI with
      | .cdecl _ _ _ T .. =>
          let ⟨T,initD,initI⟩ ← T.onAllSubtermsM initD initI (fun x d initD initI =>
            match x with
            | .fvar id =>
              match fvs.findIdx? (fun y => y == id) with
              | .none => return ⟨x,initD,initI⟩
              | .some j => return ⟨(.bvar (d + i - 1 - j)),initD,initI⟩
            | _ => return ⟨x,initD,initI⟩ )
          if i == 0
          then
            match ← IsClass? T initD initI with
            | .none => return ⟨.lam `abstractFvarWrt T term .default,initD,initI⟩
            | _ => return ⟨.lam `abstractFvarWrt T term .instImplicit,initD,initI⟩
          else
            match ← IsClass? T initD initI with
            | .none => bind (.lam `abstractFvarWrt T term .default) (i-1) initD initI
            | _ => bind (.lam `abstractFvarWrt T term .instImplicit) (i-1) initD initI
      | .ldecl _ _ _ T V nonDep .. =>
          let ⟨T,initD,initI⟩ ← T.onAllSubtermsM initD initI (fun x d initD initI =>
            match x with
            | .fvar id =>
              match fvs.findIdx? (fun y => y == id) with
              | .none => return ⟨x,initD,initI⟩
              | .some j => return ⟨(.bvar (d + i - 1 - j)),initD,initI⟩
            | _ => return ⟨x,initD,initI⟩ )
          if i == 0
          then
            return ⟨.letE `abstractFvarWrt T V term nonDep,initD,initI⟩
          else
            bind (.letE `abstractFvarWrt T V term nonDep) (i-1) initD initI
    do
    let fvS := fvs.size
    if fvS == 0
    then return ⟨e,initD,initI⟩
    else
      let ⟨absd,initD,initI⟩ ← e.onAllSubtermsM initD initI (fun x d initD initI =>
        match x with
        | .fvar id =>
          match fvs.findIdx? (fun y => y == id) with
          | .none => return ⟨x,initD,initI⟩
          | .some i => return ⟨(.bvar (d + fvS - 1 - i)),initD,initI⟩
        | _ => return ⟨x,initD,initI⟩ )
      dbg_trace "passed abs"
      bind absd (fvs.size - 1) initD initI


-- #exit

def mkValLikeCore' (N : Name) (fu body : Expr) (args : Array Expr) : TermElabM Unit := do
  let fv ← help fu
  logInfoAt (← getRef) s!"fu : {← ppExpr fu}\n{fu}"
  logInfoAt (← getRef) s!"args : {repr args}"
  let N := Name.str N "like"
  let args := args.map Expr.fvarId!
  logInfoAt (← getRef) s!"sanity 1 : {repr <| body.getFVarIds}"
  logInfoAt (← getRef) s!"sanity 2 : {repr <| (← getLCtx).decls.toArray.map (fun x => x.map (fun y => (y.fvarId, y.userName)))}"
  let .mk absed _ _ ← Lean.Expr.abstractLetFvarLam' (← getLCtx) (← getLocalInstances) args body -- ignores dependencies
  logInfoAt (← getRef) s!"absed : {← ppExpr absed}\n{absed}"
  let T ← inferType fu
  logInfoAt (← getRef) s!"T : {← ppExpr T}\n{T}"
  let lv ← getLevel T
  logInfoAt (← getRef) s!"Lv : {lv}"
  let eq := mkAppN (.const ``Eq [lv]) #[T, Expr.fvar fv, absed]
  let lvl := lv.onAllSubtermsFold [] (fun | .param n, s => s.insert n | _,s => s)
  let .mk eq _ _ ← Lean.Expr.abstractLetFvarLam (← getLCtx) (← getLocalInstances) #[fv] eq
  logInfoAt (← getRef) s!"eq : {← ppExpr eq}\n{eq}"
  let dec : Declaration := .defnDecl <| {
    name := N
    levelParams := lvl
    type := Expr.forallE N T (.sort 0) .default
    value := eq
    hints := .regular 0
    safety := .safe
  }
  addDecl dec

#check mkLambdaFVars
#check Expr.cleanupAnnotations

def Lean.Expr.cleanupAnnotations! (e : Expr) :=
  Lean.Expr.onAllSubtermsWiDepth e (fun x _ => x.cleanupAnnotations)


-- #exit

elab "add_valLike" fu:term "args" as:term,* "in" body:term : term => do
  let fu ← Elab.Term.elabTermAndSynthesize fu .none
  let fu := fu.cleanupAnnotations!
  let as := as.getElems
  let args ← as.mapM (Elab.Term.elabTermAndSynthesize · .none)
  let args := args.map .cleanupAnnotations!
  let body ← Elab.Term.elabTermAndSynthesize body .none
  let body' := body.cleanupAnnotations!
  let .some N ← getDeclName? | throwErrorAt (← getRef) "Only works for defs"
  mkValLikeCore' N fu body' args
  logInfoAt (← getRef) s!"{← getDeclName?}"
  return body


#check Meta.getLevel
#check mkLambdaFVars




@[specialize f]
partial def Lean.Expr.onAllSubterms' (e : Expr) (f : Expr → Expr) : Expr :=
  let rec @[specialize f] go (f : Expr → Expr)  (e : Expr) : Expr :=
    -- ppElabOf
    add_valLike go args f, e in
    match f e with
    | .app l r => Expr.app (go f l) (go f r)
    | .lam n l r i => .lam n (go f l) (go f r)  i
    | .forallE n l r i => .forallE n (go f l) (go f r)  i
    | .letE n l r z i => .letE n (go f l) (go f r) (go f z)  i
    | .proj n i e => .proj n i (go f e)
    | .mdata d e => .mdata d (go f e)
    | here => here
  go f e

-- add_valLike Lean.Expr.onAllSubterms.go
-- has no val you dummy

#check 1
#print Lean.Expr.onAllSubterms'.go.like


#print DefinitionSafety

#check Environment.isSafeDefinition
#print DefinitionVal


#check Elab.Term.getDeclName?

#check mkInductiveDeclEs
#print InductiveType
#print Constructor

/- todo:
- use elab decl name instead of fvar name
- look for patial consts in body and check if env have like-principles
  for them, and add them as fields to the structure that is the cuurently
  built like-principle

-/

#check Expr.rec


-- def OnAllSub (P : Expr → Prop) (e : Expr) :=
--   P e ∧
--     match e with
--     | .app l r => P l ∧ P r
--     | .lam _ l r _ => P l ∧ P r
--     | .forallE _ l r _ => P l ∧ P r
--     | .letE _ l r z _ => P l ∧ P r ∧ P z
--     | .proj _ _ e => P e
--     | .mdata _ e => P e
--     | _ => True


-- example (f : Expr → Expr) (g : (Expr → Expr) → Expr → Expr)
--   (h_g : go.like g)
--   {P : Expr → Prop}
--   (h_f :∀ e, P (f e))
--   (app : (fn arg : Expr) → P fn → P arg → P (fn.app arg))
--   (lam :
--     (binderName : Name) →
--       (binderType body : Expr) →
--         (binderInfo : BinderInfo) →
--           P binderType → P body → P (Expr.lam binderName binderType body binderInfo))
--   (forallE :
--     (binderName : Name) →
--       (binderType body : Expr) →
--         (binderInfo : BinderInfo) →
--           P binderType → P body → P (Expr.forallE binderName binderType body binderInfo))
--   (letE :
--     (declName : Name) →
--       (type value body : Expr) →
--         (nondep : Bool) → P type → P value → P body → P (Expr.letE declName type value body nondep))
--   (mdata : (data : MData) → (expr : Expr) → P expr → P (Expr.mdata data expr))
--   (proj : (typeName : Name) → (idx : Nat) → (struct : Expr) → P struct → P (Expr.proj typeName idx struct))
--   : ∀ e, P (g f e) := by
--       intro e
--       rw [h_g]
--       let fe := f e
--       have fed : fe = f e := rfl
--       dsimp
--       rw [← fed]
--       revert fed
--       induction fe with
--       | bvar => dsimp ; intro fed ; rw [fed] ; apply h_f
--       | fvar => dsimp ; intro fed ; rw [fed] ; apply h_f
--       | mvar => dsimp ; intro fed ; rw [fed] ; apply h_f
--       | const => dsimp ; intro fed ; rw [fed] ; apply h_f
--       | lit => dsimp ; intro fed ; rw [fed] ; apply h_f
--       | app l r il ir =>

      -- have :=
      --   @Expr.rec
      --     (fun x =>
      --       match x with
      --       | .bvar .. | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. =>
      --         x = f e →
      --           P (match x with
      --               | .app l r => (g f l).app (g f r)
      --               | Expr.lam n l r i => Expr.lam n (g f l) (g f r) i
      --               | Expr.forallE n l r i => Expr.forallE n (g f l) (g f r) i
      --               | Expr.letE n l r z i => Expr.letE n (g f l) (g f r) (g f z) i
      --               | Expr.proj n i e => Expr.proj n i (g f e)
      --               | Expr.mdata d e => Expr.mdata d (g f e)
      --               | here => here)
      --       | _ =>
      --         P (match x with
      --             | .app l r => (g f l).app (g f r)
      --             | Expr.lam n l r i => Expr.lam n (g f l) (g f r) i
      --             | Expr.forallE n l r i => Expr.forallE n (g f l) (g f r) i
      --             | Expr.letE n l r z i => Expr.letE n (g f l) (g f r) (g f z) i
      --             | Expr.proj n i e => Expr.proj n i (g f e)
      --             | Expr.mdata d e => Expr.mdata d (g f e)
      --             | here => here)
      --       )
      --     (fun _ => by dsimp ; intro fed ; rw [fed] ; apply h_f)
      --     (fun _ => by dsimp ; intro fed ; rw [fed] ; apply h_f)
      --     (fun _ => by dsimp ; intro fed ; rw [fed] ; apply h_f)
      --     (fun _ => by dsimp ; intro fed ; rw [fed] ; apply h_f)
      --     (fun _ _ => by dsimp ; intro fed ; rw [fed] ; apply h_f)
      --     (fun l r il ir => by
      --       dsimp at ⊢ il ir
      --       )


      -- suffices H : OnAllSub P (g f e) from H.1
      -- rw [h_g]
      -- let fe := f e
      -- have fed : fe = f e := rfl
      -- dsimp
      -- rw [← fed]
      -- revert fed
      -- induction fe with
      -- | bvar =>
      --   dsimp ; intro fed ; unfold OnAllSub
      --   constructor
      --   · rw [fed] ; apply h_f
      --   · dsimp
      -- | fvar =>
      --   dsimp ; intro fed ; unfold OnAllSub
      --   constructor
      --   · rw [fed] ; apply h_f
      --   · dsimp
      -- | mvar =>
      --   dsimp ; intro fed ; unfold OnAllSub
      --   constructor
      --   · rw [fed] ; apply h_f
      --   · dsimp
      -- | sort =>
      --   dsimp ; intro fed ; unfold OnAllSub
      --   constructor
      --   · rw [fed] ; apply h_f
      --   · dsimp
      -- | const =>
      --   dsimp ; intro fed ; unfold OnAllSub
      --   constructor
      --   · rw [fed] ; apply h_f
      --   · dsimp
      -- | app l r il ir =>
      --   intro q
      --   dsimp
      --   unfold OnAllSub at *


--add_valLike go args f, e in

partial def test1 (n : Nat) : Nat :=
  add_valLike test1 args n in
  test1 (n+1)


#print test1.like


example (f : Nat → Nat) (h : test1.like f)
  : ∃ c, f = (fun _ => c) := by
    let x := f 0
    refine ⟨x, ?_⟩
    funext n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [h] at ih
      dsimp at ih
      exact ih



@[specialize f]
partial def Lean.Expr.onAllSubtermsWiDepth' (e : Expr) (f : Expr → Nat → Expr) : Expr :=
  let rec @[specialize f] go (f : Expr → Nat → Expr) (e : Expr) (d : Nat) : Expr :=
    add_valLike go args f, e, d in
    match f e d with
    | .app l r => Expr.app (go f l d) (go f r d)
    | .lam n l r i => .lam n (go f l d) (go f r (d+1))  i
    | .forallE n l r i => .forallE n (go f l d) (go f r (d+1))  i
    | .letE n l r z i => .letE n (go f l d) (go f r d) (go f z (d+1))  i
    | .proj n i e => .proj n i (go f e d)
    | .mdata md e => .mdata md (go f e d)
    | here => here
  go f e 0

def Lean.Expr.abstractPat' (pat within : Expr) : Expr :=
  within.onAllSubtermsWiDepth' (fun x d =>
    if x == pat
    then
      .bvar d
    else
      match x with
      | .bvar i => if i ≥ d then .bvar (i+1) else x
      | _ => x
    )


def Lean.Expr.hasNoLooseBvar (d := 0) : Expr → Prop
  | .app l r => l.hasNoLooseBvar d ∧ r.hasNoLooseBvar d
  | .lam _ l r _ => l.hasNoLooseBvar d ∧ r.hasNoLooseBvar (d+1)
  | .forallE _ l r _ => l.hasNoLooseBvar d ∧ r.hasNoLooseBvar (d+1)
  | .letE _ l r z _ => l.hasNoLooseBvar d ∧ r.hasNoLooseBvar d ∧ z.hasNoLooseBvar (d+1)
  | .proj _ _ e => e.hasNoLooseBvar d
  | .mdata _ e => e.hasNoLooseBvar d
  | .bvar i => i < d
  | _ => True

theorem Lean.Expr.hasNoLooseBvar_succ
  (d : Nat) (e : Expr) (h : e.hasNoLooseBvar d) : e.hasNoLooseBvar (d+1) := by
    induction e generalizing d with
    | bvar i =>
      dsimp [Lean.Expr.hasNoLooseBvar] at *
      grind
    | fvar _ | mvar _ | sort _ | const _ | lit _ =>
      trivial
    | proj _ _ e ih | mdata _ e ih =>
       dsimp [Lean.Expr.hasNoLooseBvar] at *
       exact ih d h
    | app l r il ir =>
      dsimp [Lean.Expr.hasNoLooseBvar] at *
      exact .intro (il d h.1) (ir d h.2)
    | lam _ l r _ il ir | forallE _ l r _  il ir =>
      dsimp [Lean.Expr.hasNoLooseBvar] at *
      exact .intro (il d h.1) (ir (d+1) h.2)
    | letE _ l r z _ il ir iz =>
      dsimp [Lean.Expr.hasNoLooseBvar] at *
      exact .intro (il d h.1) <| .intro (ir d h.2.1) (iz (d+1) h.2.2)




example (pat within : Expr)
  (h : ∀ i, pat ≠ .bvar i) [LawfulBEq Expr] (d : Nat)
  (hp : pat.hasNoLooseBvar d) (hw : within.hasNoLooseBvar d) :
  let f := (fun x d =>
    if x == pat
    then
      .bvar d
    else
      match x with
      | .bvar i => if i ≥ d then .bvar (i+1) else x
      | _ => x
    )
  ∀ g, Lean.Expr.onAllSubtermsWiDepth'.go.like g →
    (g f within d).hasNoLooseBvar (d+1) := by
      intro f g hg
      induction within generalizing d with
      | bvar i =>
        rw [hg]
        dsimp
        if q : (.bvar i) == pat
        then
          exfalso
          apply h i
          exact (eq_of_beq q).symm
        else
          have : f (Expr.bvar i) d = if i ≥ d then .bvar (i+1) else .bvar i := by
            dsimp [f] ; rw [if_neg q]
          split at this
          · rename_i q
            rw [this]
            dsimp [Lean.Expr.hasNoLooseBvar] at ⊢ hw
            grind
          · rename_i q
            rw [this]
            dsimp [Lean.Expr.hasNoLooseBvar] at ⊢
            apply Nat.lt_of_lt_of_le (Nat.lt_of_not_le q) (Nat.le_add_right d 1)
      | fvar fv =>
        rw [hg]
        dsimp
        if q : (.fvar fv) == pat
        then
          have : f (Expr.fvar fv) d = .bvar d := by
            dsimp [f] ; rw [if_pos q]
          rw [this]
          dsimp [Lean.Expr.hasNoLooseBvar]
          exact Nat.lt_add_one d
        else
          have : f (Expr.fvar fv) d = .fvar fv := by
            dsimp [f] ; rw [if_neg q]
          rw [this]
          dsimp [Lean.Expr.hasNoLooseBvar]
      | app l r il ir =>
        dsimp [Lean.Expr.hasNoLooseBvar] at hw
        specialize il d hp hw.1
        specialize ir d hp hw.2
        rw [hg]
        dsimp
        if q : (.app l r) == pat
        then
          have : f (Expr.app l r) d = .bvar d := by
            dsimp [f] ; rw [if_pos q]
          rw [this]
          dsimp [Lean.Expr.hasNoLooseBvar]
          exact Nat.lt_add_one d
        else
          have : f (Expr.app l r) d = .app l r := by
            dsimp [f] ; rw [if_neg q]
          rw [this]
          dsimp [Lean.Expr.hasNoLooseBvar]
          exact .intro il ir
      | lam n l r b il ir =>
        dsimp [Lean.Expr.hasNoLooseBvar] at hw
        specialize il d hp hw.1
        specialize ir (d+1) (Lean.Expr.hasNoLooseBvar_succ d _ hp) hw.2
        rw [hg]
        dsimp
        if q : (.lam n l r b) == pat
        then
          have : f (Expr.lam n l r b) d = .bvar d := by
            dsimp [f] ; rw [if_pos q]
          rw [this]
          dsimp [Lean.Expr.hasNoLooseBvar]
          exact Nat.lt_add_one d
        else
          have : f (Expr.lam n l r b) d = .lam n l r b := by
            dsimp [f] ; rw [if_neg q]
          rw [this]
          dsimp [Lean.Expr.hasNoLooseBvar]
          exact .intro il ir
      | _ => sorry
