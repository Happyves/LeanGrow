
import LeanGrow.F.Utils.ExprTrieRW.Query

import Lean

open Lean

-- build expression with recursors from
#check RWblueprint


#check Eq.rec
#check Eq.ndrec


def CExpr.factor (on : CExpr) (dirs : List rwDirs) (type : CExpr) : CExpr :=
  let rec go (depth : Nat) : CExpr → List rwDirs → CExpr
    | .lam n t b i , d :: more =>
          match d with
          | .left => .lam n (go depth t more) b i
          | .right => .lam n t (go (depth+1) b more) i
          | _ => .failed
    | .forallE n t b i , d :: more =>
          match d with
          | .left => .forallE n (go depth t more) b i
          | .right => .forallE n t (go (depth+1) b more) i
          | _ => .failed
    | .letE n t v b i  , d :: more=>
          match d with
          | .left => .letE n (go depth t more) v b i
          | .mid => .letE n t (go depth v more) b i
          | .right => .letE n t v (go (depth+1) b more) i
    | .app l r, d :: more =>
        match d with
          | .left => .app (go depth l more) r
          | .right => .app l (go depth r more)
          | _ => .failed
    | .proj n i e, d :: more =>
        match d with
          | .left => .proj n i (go depth e more)
          | _ => .failed
    | _, _ :: _  => .failed
    | _, [] => .bvar depth
  .lam `LenGrow.EqFacto (type) (go 0 on dirs) .default

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

-/
