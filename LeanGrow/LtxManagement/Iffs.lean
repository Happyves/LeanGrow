
import Lean

open Lean Meta Elab Tactic

#check Iff

#check Iff.mp

#check LocalContext

#check MVarId.assert
#check MVarId.define
#check MVarId.intro1P

#check liftMetaTactic


elab "handle_iffs_left" : tactic => do
  let ltx ← getLCtx
  --let g ← getMainTarget
  let FVS := ltx.getFVars
  for f in FVS do
    let tf ← withMainContext (inferType f)
    match tf with
    | .app (.app (.const `Iff []) l) r => do
        let mut L? := Option.none
        for c in FVS do
          let tc ← withMainContext (inferType c)
          if ← isDefEq l tc -- probably mvar assignement issues here
          then L? := .some c
        match L? with
        | .some L =>
              liftMetaTactic fun mvarId => do
                let mvarIdNew ← mvarId.assert (Name.str (← f.fvarId!.getUserName) "lefty") r (.app (.app (.app (.app (.const `Iff.mp []) l) r) f) L)
                let (_, mvarIdNew) ← mvarIdNew.intro1P
                return [mvarIdNew]
        | .none => pure ()
    | _ => pure ()

example (A B : Prop) (a : A) (h : A ↔ B) : B :=
  by
  handle_iffs_left
  exact h.lefty

 /-
 Todo
 - handle mutiple iffs
 - handle right iffs
 -/

#check MVarId.assertHypotheses

elab "handle_iffs" : tactic => do
  let ltx ← getLCtx
  let FVS := ltx.getFVars
  let mut Hs : Array Hypothesis := #[]
  for f in FVS do
    let fn ← f.fvarId!.getUserName
    let tf ← withMainContext (inferType f)
    match tf with
    | .app (.app (.const `Iff []) l) r => do
        let mut L? := #[]
        let mut R? := #[]
        for c in FVS do
          let tc ← withMainContext (inferType c)
          let dl ← isDefEq l tc
          let dr ← isDefEq r tc
          if  dl && L?.isEmpty -- probably mvar assignement issues here
          then L? := L?.push c
          if dr && R?.isEmpty -- probably mvar assignement issues here
          then R? := R?.push c
          if !(L?.isEmpty) && !(R?.isEmpty)
          then break
        let HL : Array Hypothesis := L?.map (fun e => ⟨(Name.str fn "lefty"), r, (.app (.app (.app (.app (.const `Iff.mp []) l) r) f) e)⟩)
        let HR : Array Hypothesis := R?.map (fun e => ⟨(Name.str fn "righty"), l, (.app (.app (.app (.app (.const `Iff.mpr []) l) r) f) e)⟩)
        Hs := Array.append (Array.append Hs HR) HL
    | _ => pure ()
  liftMetaTactic fun mvarId => do
    let (_,g) ← mvarId.assertHypotheses Hs
    return [g]

example (A B : Prop) (a : A) (h : A ↔ B) : B :=
  by
  handle_iffs
  exact h.lefty

example (A B : Prop) (a : B) (h : A ↔ B) : A :=
  by
  handle_iffs
  exact h.righty

example (A B : Prop) (a : A) (b : B) (h : A ↔ B) : True :=
  by
  handle_iffs
  trivial

example (A B : Prop) (a : A) (b : B) (c : B) (h : A ↔ B) : True :=
  by
  handle_iffs
  trivial

example (A B  C D: Prop) (a : A) (b : B) (c : C) (h1 : A ↔ B) (h2 : C ↔ D): True :=
  by
  handle_iffs
  trivial

example (A B C : Prop) (a : A) (b : B) (c : C) (h1 : A ↔ B) (h2 : B ↔ C): True :=
  by
  handle_iffs
  trivial
