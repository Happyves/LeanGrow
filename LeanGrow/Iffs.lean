
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
                let mvarIdNew ← mvarId.assert (Name.str (← f.fvarId!.getUserName) "lefty") r (.app (.app (.const `Iff.mp []) f) L)
                let (_, mvarIdNew) ← mvarIdNew.intro1P
                return [mvarIdNew]
        | .none => pure ()
    | _ => pure ()

example (A B : Prop) (a : A) (h : A ↔ B) : True :=
  by
  handle_iffs_left
  trivial
