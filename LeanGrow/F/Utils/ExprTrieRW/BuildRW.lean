
import LeanGrow.F.Utils.ExprTrieRW.Query
import LeanGrow.F.Data.CExpr.ReduceInferMuggle.Control

import Lean

open Lean

-- build expression with recursors from
#check RWblueprint


#check Eq.rec
#check Eq.ndrec


def CExpr.factor (on : CExpr) (dirs : List rwDirs) (type : CExpr) : (CExpr × CExpr) :=
  let rec go (depth : Nat) : CExpr → List rwDirs → (CExpr × CExpr)
    | .lam n t b i , d :: more =>
          match d with
          | .left => let (F,R) := (go depth t more) ; (.lam n F b i, R)
          | .right =>let (F,R) := (go (depth+1) b more) ; (.lam n t F i, R)
          | _ => (.failed, .failed)
    | .forallE n t b i , d :: more =>
          match d with
          | .left => let (F,R) := (go depth t more) ; (.forallE n F b i, R)
          | .right => let (F,R) := (go (depth+1) b more) ;  (.forallE n t F i, R)
          | _ => (.failed, .failed)
    | .letE n t v b i  , d :: more=>
          match d with
          | .left => let (F,R) := (go depth t more); (.letE n F v b i, R)
          | .mid => let (F,R) := (go depth t more) ; (.letE n t F b i, R)
          | .right => let (F,R) := (go (depth+1) b more) ; (.letE n t v F i, R)
    | .app l r, d :: more =>
        match d with
          | .left => let (F,R) := (go depth l more) ; (.app F r, R)
          | .right => let (F,R) := (go depth r more) ;  (.app l F, R)
          | _ => (.failed, .failed)
    | .proj n i e, d :: more =>
        match d with
          | .left => let (F,R) := (go depth e more) ; (.proj n i F, R)
          | _ => (.failed, .failed)
    | _, _ :: _  => (.failed, .failed)
    | ce, [] => (.bvar depth, ce)
  let (F,R) := (go 0 on dirs)
  (.lam `LeanGrow.EqFacto (type) F .default, R)



/-
Alternatively, when we generate the Eq-thms-cache-thing for rewrites, we can take note of the type
in the rw theorem ; the type should have to get filled out when embedding the epxression-thm-thing
we'll then use this type for the motive and Eq.ndrec (the α)
-/

open Meta Elab Term Tactic

#check MVarId
#check reduce
#check elabTermAndSynthesize
#check mkFreshExprMVar
#check synthesizeSyntheticMVarsNoPostponing


elab "testingMvars" : tactic => withMainContext <|  withSynthesize <| do
      let ref ← getRef
      let mv ← mkFreshExprMVar .none .natural
      let term : Expr := .lam `testin mv (.app (.const `Nat.succ []) (.bvar 0)) .default
      let elabed? ← instantiateMVars (← withSynthesize (do synthesizeSyntheticMVarsNoPostponing ; return term))
      let T ← instantiateMVars  (← inferType term)
      let elabed?? ← instantiateMVars term
      let _ ← withSynthesize (isDefEq term (.const `Unit []))
      let elabed??? ← instantiateMVars term
      logInfoAt ref s!"{repr elabed?}\n{repr T}\n{repr elabed??}\n{repr elabed???}"

example : True := by
      testingMvars
      trivial


elab "testingMvars2" : tactic => withMainContext do
      let sin : Syntax ← `(fun testin => Nat.succ testin)
      let test ← Term.elabTerm sin .none
      logInfoAt (← getRef) s!"{repr test}"

example : True := by
      testingMvars2
      trivial

#check mkAppM
#check mkCongrFun

#check Lean.Meta.Tactic.TryThis.addTermSuggestions

/-
As of now, the idea is to get the type as follows:

- When we extract Eq-thms, we get either side and the type of these terms in Eq, ; when embedding,
  the type should get assigned ?

- If that doesn't work, add an mvar constructor to CExpr, and resort to turning the expressions
  to actual strings, then parsing and elaborating them, since handling mvars directly seems to
  be a pain in the ass


**Note**
We should also do this for HEq and Iff ?
-/

#check Option.map.eq_1

/-
In new versions:
`Option.map.eq_2.{u_1, u_2} {α : Type u_1} {β : Type u_2} (f : α → β) : Option.map f none = none`
Seems not embeddable in `Option.map (fun x => Nat.succ x) .none` ?
At least, it seems not possible to find β without deriving a type, somehow...

This is actually already a problem in our embedding algos... Say if we tried to goal-embed the above,
with f = (fun x => Nat.succ x), then we'd get an .ofCExpr, which wouldn't propagate as we don't know
its type
-/


#check Eq.rec
#check Eq.ndrec

set_option pp.all true in
#check @Eq.ndrec _ (1+1) (fun x : Nat => x = 2) (rfl : (1+1) = 2) (4-2) (rfl : (1+1) = (4-2))


theorem testRW : (1+1 = 2) = (4-2 = 2) := rfl

#print testRW
-- not prop eq of inhabited, actual reudction must have occured


/--
Wrt Eq.ndrec type:
on is m ; subs is b ; subsType is α ; init is a ; factor is motive ; rw_thmis h
-/
def CExpr.buildRW (fctx : FixCtx) (rw_thm : CExpr) (subs on : CExpr) (dirs : List rwDirs) : CExpr :=
      let subsType := CExpr.whnf fctx (CExpr.inferType fctx subs)
      let onType := CExpr.whnf fctx (CExpr.inferType fctx on)
      -- ↑ is required for β to be reduced in repeated rewriting
      -- however, it then requires that the `dirs` are wrt. the *reduced* type of on !!!
      let (factor, init) := CExpr.factor onType dirs subsType
      let motiveType := CExpr.inferType fctx factor
      match subsType, motiveType with
      | .sort u2, .forallE _ _ (.sort u1) _ =>
            CExpr.mkApp (.const `Eq.ndrec [u1,u2]) [subsType, init, factor, on, subs, rw_thm]
      | _,_ => .failed


def CExpr.buildRWs (fctx : FixCtx) (rw_data : List (CExpr × CExpr × (List rwDirs))) (on : CExpr) : CExpr :=
      let rec go (on' : CExpr) : List (CExpr × CExpr × (List rwDirs)) → CExpr
            | (rw_thm, subs, dirs) :: more =>
                  let step := CExpr.buildRW fctx rw_thm subs on' dirs
                  go step more
            | [] => on'
      go on rw_data
