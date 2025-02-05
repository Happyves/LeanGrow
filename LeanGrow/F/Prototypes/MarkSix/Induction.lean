
import Lean
import LeanGrow.F.Data.CExpr.ReduceInferMuggle.Reduce

-- # Play

#check Nat.noConfusion
#check List.noConfusion

example (n : Nat) : 0 ≠ n.succ := Nat.noConfusion


example (n : Nat) : 0 ≠ n.succ := by
  intro con
  apply Nat.noConfusion con

theorem testinNC (n : Nat) (con : n.succ = 0) : 2+2 = 5 := by
  apply Nat.noConfusion con


#check Lean.mkNoConfusionCoreImp
#check Lean.Meta.mkNoConfusion

#print testinNC

--#exit

/-
For noConfusion :
At each forward step, scan if eq of two dsitinct constructors, and if so,
solve every goal of the IntroTree targets with the noConfusion theorem
-/


#check Lean.Meta.mkInjectiveTheorems
#check Nat.succ.inj
#check List.cons.inj

theorem Nat.succ.inj' {m n : Nat} : m.succ = n.succ → m = n :=
  by
  intro x
  apply Nat.noConfusion x
  apply id


example {m n : Nat} : m.succ = n.succ → True :=
  by
  intro x
  apply Nat.noConfusion x
  intro inj
  apply True.intro

/-
For injectivity:
do nothing ?
Seems like a regular theorem that an be used as forward/backward
step. Check that it is contained in the environement though, when
we generate our version of it.
Maybe also split theorems on all the ∧

-/

#check Lean.Meta.mkRecursorAppPrefix

#check Nat.rec
#check Nat.casesOn

#check Lean.mkCasesOn
#check mkRecOn

#check Exists.rec
-- only for Prop
#check PSigma.rec

/-
For recursors:
Scan goal type for inductive sub-terms (figure out how to do this without
allways calling inferType on everything ?) and factor goal type into a
motive, and keep the sub-term as major arg
Then treat the remainding args as in a backstep
Don't forget structures !

-/

#check Quot.ind
#check Quotient.ind
#check Quot.rec
#check Quotient.rec
-- same as with recursors ; note that we should delta types to check if they aren't quotients
-- in disguise, or maybe even mark them in a preprocessing step
#check Quot.hrecOn
#check Quotient.hrecOn


-- Maybe also size opportunity to support exfalso:
-- should just check if forward step adds False, in which case
-- we solve all goals of the IntroTree with it
#check False.elim
#check False.rec


-- make sure to check that ext lemmas will also land in our version of environment
#check Prod.ext



/-
↓ The matches are just repeated recursors,
-/

def fac : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * fac n

#check fac.eq_1
#check fac.eq_2
#check fac.eq_def
#check fac.match_1
#print fac.match_1


def fib : Nat → Nat
  | 0 => 1
  | 1 => 1
  | n+2 => fib (n+1) * fib n

#check fib.match_1
#print fib.match_1

def ackermann : Nat → Nat → Nat
  | 0, m => m + 1
  | n+1, 0 => ackermann n 1
  | n+1, m+1 => ackermann n (ackermann (n + 1) m)

#check ackermann.match_1
#print ackermann.match_1

#check 1

/-
Maybe we can check if there are functions in the goal that have such a matcher,
add factor the goal into the motive of match_1, where the factor on the function
inputs. This way, in each subgoal, we can unfold the function efforlessly.
Replace this by Joachim Breitners functional induction at some point.

-/



-- # NoConfusion


#check Ne

open Lean Elab Meta Term

elab "testin" t:term : command => Command.liftTermElabM do
  let e ← elabTermAndSynthesize t .none
  IO.println (repr e)

testin (0 ≠ 2)
testin ¬ (0 = 2)
testin (0 = 2) → False

def tryNoConfusion (fctx : FixCtx) (ltxType : CExpr) : Option CExpr :=
  let main (T l r : CExpr) : Option CExpr :=
    let (T', params) := (CExpr.whnf fctx T).getApp
    match T' with
    | .const n us =>
        let N := n.toString
        match fctx.cstData.find? N with
        | .some (.indu _ _ _) =>
            let (l',_) := (CExpr.whnf fctx l).getApp
            let (r',_) := (CExpr.whnf fctx r).getApp
            match l', r' with
            | .const nl _, .const nr _ =>
                match fctx.cstData.find? nl.toString, fctx.cstData.find? nr.toString with
                | .some (.ctor _ _ clV), .some (.ctor _ _ crV) =>
                    if clV.cidx != crV.cidx
                    then
                      let proof_of_false :=
                        .app (
                          .app (
                            .app (
                              .app ((CExpr.const (Name.str (Name.str Name.anonymous N) "noConfusion") (us ++ [0])).mkApp params) (.const `False [])
                               ) l ) r ) ltxType
                      .some proof_of_false
                    else
                      .none
                | _, _ => .none
            | _, _ => .none
        | _ => .none
    | _ => .none
  match ltxType with
  | .app (.app (.app (.const `Ne _) T ) l) r => main T l r
  | .app (.const `Not _) (.app (.app (.app (.const `Eq _) T ) l) r) => main T l r
  | .forallE _ (.app (.app (.app (.const `Eq _) T ) l) r) (.const `False _) _ => main T l r
  | _ => .none


#check Nat.noConfusion
testin False
#check False
#check Name
#check List.noConfusion
#check List

/-
Next, run exfalso trigger on the proof of false, in case there is
-/


#check_failure Nat.le.noConfusion
-- FIX IN ABOVE : discard predicates


-- # Induction

/-
Nachlass:
- induct on gnodes only ?
- else, also constants and applicaitons with fun has induc at head of type
- add info if binding type is induc/qot in binder ?
- revert all props depending on the gnode into the motive
  (then solve goal by adding them back into an app on the rec proof term)
- For inductive predicates (or parameterised inductives), revert subterms ?

-/


#check Eq.rec
#check Exists.rec
#check Nat.le.rec
#check List.Mem.rec

-- # Exfalso

-- # Induct on fun matcher
