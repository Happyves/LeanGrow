
import LeanGrow.F.Utils.ExprTrieRW.Query
import LeanGrow.F.Data.CExpr.ReduceInferMuggle.Control
import LeanGrow.F.Utils.ExprTrieRW.RWclasses

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
on is m ; subs is b ; subsType is α ; init is a ; factor is motive ; rw_thm is h
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


#check Eq.rec
#check Eq.ndrec

def dirsToRWinsts (classes : List (Nat × RWClassData)) (dirs : List (Nat × List Nat × List rwDirs)) : List (CExpr × List rwDirs) :=
      let rec go (done : List (CExpr × List rwDirs)) : List (Nat × List Nat × List rwDirs) → List (CExpr × List rwDirs)
            | [] => done.reverse
            | (cid, ind, ld) :: moe =>
                  match classes.find? (fun x => x.1 == cid) with
                  | .none => []
                  | .some (_, cData) =>
                        match ind.head? with
                        | .none => [] -- ignores other indices... ; might yield bugs
                        | .some I =>
                              match cData.class_cexprs.find? (fun x => x.1 == I) with
                              | .none => []
                              | .some (_,ce) =>
                                    go ((ce, ld) :: done) moe
            go [] dirs


/- Should produce a thm `a = b`
where `a` is in the desired pattern and `b` is whats assembled from the blueprint
from the context, with its rw-classes.

Conceptual note
-/
-- partial def CExpr.buildRWofBluePrint
--       (fctx : FixCtx)
--       (classes : List (Nat × RWClassData))
--       (mainData : List (Nat × CExpr))
--       (bp : RWblueprint Nat) (query : CExpr) : CExpr :=
--       -- we expect `query` to be the expression who's query the blueprint was built from.
--       let rec go : RWblueprint Nat → CExpr
--             | .exactMatch classId entryId ind =>
--                   match classId, entryId with
--                   | .none, _ =>
--                         match ind.head? with
--                         | .none => .failed
--                         | .some I =>
--                               match mainData.find? (fun x => x.1 == I) with
--                               | .none => .failed
--                               | .some (_,ce) =>
--                                     let cet := (ce.inferType fctx).whnf fctx
--                                     match cet with
--                                     | .sort u => CExpr.mkApp (.const `Eq.refl [u]) [cet, ce]
--                                     | _ => .failed
--                   | .some cId, .some eId =>
--                         match classes.find? (fun x => x.1 == cId) with
--                         | .none => .failed
--                         | .some (_, cData) =>
--                               match ind.head? with
--                               | .none => .failed
--                               | .some I =>
--                                     buildEqThm cData.class_type cData.class_type_level cData.class_cexprs cData.base cData.class_graph eId I
--                                     -- match cData.class_cexprs.find? (fun x => x.1 == I) with
--                                     -- | .none => .failed
--                                     -- | .some (_,ce) =>
--                                     --       let cet := cData.class_type
--                                     --       match cet with
--                                     --       | .sort u =>

--                                     --             CExpr.mkApp (.const `Eq.refl [u]) [cet, ce]
--                                     --       | _ => .failed
--                   | _, _ => .failed
--             | .node classId entryId ind dirs chi =>
--                   let rwData := dirsToRWinsts classes dirs
--                   let thms := chi.map go
--                   let joined := List.zip thms rwData
--                   match ind.head? with
--                   | .none => .failed
--                   | .some I =>
--                         match classId, entryId with
--                         | .none, _ =>
--                               match mainData.find? (fun x => x.1 == I) with
--                               | .none => .failed
--                               | .some (_,ce) =>
--                                     CExpr.buildRWs fctx joined ce
--                         | .some cId, .some eId =>
--                               match classes.find? (fun x => x.1 == cId) with
--                               | .none => .failed
--                               | .some (_, cData) =>
--                                     match cData.class_cexprs.find? (fun x => x.1 == I), cData.class_cexprs.find? (fun x => x.1 == eId) with
--                                     | .some (_,ce), .some (_,ceE) =>
--                                           let sofar := CExpr.buildRWs fctx joined ce
--                                           let inClass := buildEqThm cData.class_type cData.class_type_level cData.class_cexprs cData.base cData.class_graph eId I
--                                           CExpr.mkApp (.const `Eq.trans [cData.class_type_level]) [ceE,ce,query,inClass,sofar]
--                                     | _, _ =>  .failed

--                         | _, _ => .failed
--       go bp

-- TODO: testing and debug

#check 1

/-
State of things:

In the above, `a`, `b` and their equality may appear in different contexts:
- We could have the goal `a = b`. In that case, we would like to build blueprints
  for both `a` and `b` from the local context (possibly exact matches) so as
  to get `a=A` and `b=B` where `A` and `B` are built via rws from local context.
  We then try to prve `A=B` ?


Short term goals:
Given an RW-thm, find occurences one of the sides in the ltx trie, check
if RW thm applies by attempting to embed its assumption, add RW node, add
or modify RW class.
Make unification up to rewrites: a queried type wih untaged lnodes should
be found in the form of a RWblueprint, with some format for unification.
Then, we should try to build the terms...

-/


#check Eq.ndrec

#check id

example {Even : Nat → Prop} (n m: Nat) (h : Even n) (eq : n = m) : Even m :=
      @Eq.ndrec _ n _ h m eq

#check @Eq.ndrec Type Nat id (by dsimp ; exact 42) Nat rfl
#eval @Eq.ndrec Type Nat id (by dsimp ; exact 42) Nat rfl

#check Eq.subst
#check Eq.trans
#check propext


def CExpr.getOfDirs : CExpr → List rwDirs → CExpr
      | .app l _, .left :: more => l.getOfDirs more
      | .app _ r, .right :: more => r.getOfDirs more
      | .lam _ l _ _, .left :: more => l.getOfDirs more
      | .lam _ _ r _, .right :: more => r.getOfDirs more
      | .forallE _ l _ _, .left :: more => l.getOfDirs more
      | .forallE _ _ r _, .right :: more => r.getOfDirs more
      | .letE _ l _ _ _, .left :: more => l.getOfDirs more
      | .letE _ _ m _ _, .mid :: more => m.getOfDirs more
      | .letE _ _ _ r _, .right :: more => r.getOfDirs more
      | .proj _ _ l, .left :: more => l.getOfDirs more
      | ce, [] => ce
      | _,_ => .failed



partial def CExpr.buildRWofBluePrint_2
      (fctx : FixCtx)
      (classes : List (Nat × RWClassData))
      (mainData : List (Nat × CExpr))
      (bp : RWblueprint Nat) (query : CExpr) : CExpr :=
      let rec go (query_sub : CExpr) : RWblueprint Nat → CExpr
            | .exactMatch classId entryId ind =>
                  match classId, entryId with
                  | .none, _ =>
                        match ind.head? with
                        | .none => .failed
                        | .some I =>
                              match mainData.find? (fun x => x.1 == I) with
                              | .none => .failed
                              | .some (_,ce) =>
                                    let cet := (ce.inferType fctx).whnf fctx
                                    match cet with
                                    | .sort u => CExpr.mkApp (.const `Eq.refl [u]) [cet, ce]
                                    | _ => .failed
                  | .some cId, .some eId =>
                        match classes.find? (fun x => x.1 == cId) with
                        | .none => .failed
                        | .some (_, cData) =>
                              match ind.head? with
                              | .none => .failed
                              | .some I =>
                                    buildEqThm cData.class_type cData.class_type_level cData.class_cexprs cData.base cData.class_graph eId I
                  | _, _ => .failed
            | .node classId entryId ind dirs chi =>
                  let rwData := dirsToRWinsts classes dirs
                  let temp := List.zipWith (fun x y => (x.2.2,y) ) dirs chi
                  let thms := temp.map (fun (d, bp) => go (query_sub.getOfDirs d) bp )
                  let joined := List.zip thms rwData
                  match ind.head? with
                  | .none => .failed
                  | .some I =>
                        match classId, entryId with
                        | .none, _ =>
                              match mainData.find? (fun x => x.1 == I) with
                              | .none => .failed
                              | .some (_,ce) =>
                                    CExpr.buildRWs fctx joined ce
                        | .some cId, .some eId =>
                              match classes.find? (fun x => x.1 == cId) with
                              | .none => .failed
                              | .some (_, cData) =>
                                    match cData.class_cexprs.find? (fun x => x.1 == I), cData.class_cexprs.find? (fun x => x.1 == eId) with
                                    | .some (_,ce), .some (_,ceE) =>
                                          let sofar := CExpr.buildRWs fctx joined ce
                                          let inClass := buildEqThm cData.class_type cData.class_type_level cData.class_cexprs cData.base cData.class_graph eId I
                                          CExpr.mkApp (.const `Eq.trans [cData.class_type_level]) [ceE,ce,query_sub,inClass,sofar]
                                    | _, _ =>  .failed

                        | _, _ => .failed
      go query bp


/-
In the above we seemingly build the blueprint from the bottom up.

It would be intresting to build them from top to down.
For example, in the nested rw example of the query file, where we have blueprint:
RWblueprint.node none none [1]
  [(37, [1], [rwDirs.left])]
  [RWblueprint.node (some 37) (some 1) [2]
      [(42, [2], [rwDirs.left])]
      [RWblueprint.exactMatch (some 42) (some 1) [2]]]
We would get 1 of the mainData, ie. `(a b) c`.
Then, we factor it according to `[rwDirs.left]` and use the
info that that term should be replaced with the term of index 2
in class 37.
We would then build the term `(x y) c` using the previous factor as motive,
and the inner class (37) eaulity theorem as eq-thm from 1 to 2 in `Eq.ndrec`.
Then with that term, we procced, where we should add `[rwDirs.left]` as a prifix
to the next rw-dirs.
So next, `(x y) c` should be factored according to `[rwDirs.left,rwDirs.left]`
and that term should be replaced by that of index 2 in class 42.
We would then build the term `(z y) c` using the previous factor as motive,
and the inner class (42) eaulity theorem as eq-thm from 1 to 2 in `Eq.ndrec`.
-/


partial def CExpr.buildRWofBluePrint_3
      (fctx : FixCtx)
      (classes : List (Nat × RWClassData))
      (mainData : List (Nat × CExpr)) -- gnodes with type
      (BP : RWblueprint Nat) : CExpr :=
      let rec go (term type Ttype : CExpr) : List (List rwDirs × RWblueprint Nat) → CExpr
      | [] => term
      | (dirs, bp) :: more =>
            match bp with
            | .exactMatch classId entryId ind =>
                  match classId, entryId with
                  | .none, _ => .failed
                  | .some cId, .some eId =>
                        match classes.find? (fun x => x.1 == cId) with
                        | .none => .failed
                        | .some (_, cData) =>
                              match ind.head? with
                              | .none => .failed
                              | .some I =>
                                    match cData.class_cexprs.find? (fun x => x.1 == I) with
                                    | .some (_,ce) => -- the term corresponding to eId should be that that will get factored
                                          --let Ttype := CExpr.whnf fctx (CExpr.inferType fctx type) -- can it change durring rws ? if not, store it as param
                                          let (motive, ceE) := CExpr.factor type dirs Ttype
                                          let inClass := buildEqThm cData.class_type cData.class_type_level cData.class_cexprs cData.base cData.class_graph eId I
                                          let motiveType := CExpr.inferType fctx motive
                                          match Ttype, motiveType with -- level of Ttype should be param
                                          | .sort u2, .forallE _ _ (.sort u1) _ =>
                                                let rwed := CExpr.mkApp (.const `Eq.ndrec [u1,u2]) [Ttype, ceE, motive, type, ce, inClass]
                                                let nweType := CExpr.whnf fctx (.app motive ce)
                                                go rwed nweType Ttype more
                                          | _, _ => .failed
                                    | _ => .failed
                  | _, _ => .failed
            | .node classId entryId ind ndirs chi =>
                  match classId, entryId with
                  | .some cId, .some eId =>
                        match classes.find? (fun x => x.1 == cId) with
                        | .none => .failed
                        | .some (_, cData) =>
                              match ind.head? with
                              | .none => .failed
                              | .some I =>
                                    match cData.class_cexprs.find? (fun x => x.1 == I) with
                                    | .none => .failed
                                    | .some (_,ce) =>
                                          let (motive, ceE) := CExpr.factor type dirs Ttype
                                          let inClass := buildEqThm cData.class_type cData.class_type_level cData.class_cexprs cData.base cData.class_graph eId I
                                          let motiveType := CExpr.inferType fctx motive
                                          match Ttype, motiveType with -- level of Ttype should be param
                                          | .sort u2, .forallE _ _ (.sort u1) _ =>
                                                let rwed := CExpr.mkApp (.const `Eq.ndrec [u1,u2]) [Ttype, ceE, motive, type, ce, inClass]
                                                let nweType := CExpr.whnf fctx (.app motive ce)
                                                let todos := List.zipWith (fun d bp => (dirs ++ d.2.2, bp)) ndirs chi
                                                go rwed nweType Ttype (todos ++ more)
                                          | _, _ => .failed
                  | _, _ => .failed -- none is expected to be handled before calls to go
      match BP with
      | .exactMatch .none .none ind =>
            match ind.head? with
            | .none => .failed
            | .some I => .gnode I (.ofBvar 42)
      | .node .none .none ind ndirs chi =>
            match ind.head? with
            | .none => .failed
            | .some I =>
                  match mainData.find? (fun x => x.1 == I) with
                  | .none => .failed
                  | .some (_,ce) =>
                        let Ttype := CExpr.whnf fctx (CExpr.inferType fctx ce)
                        let todos := List.zipWith (fun d bp => (d.2.2, bp)) ndirs chi
                        go (.gnode I (.ofBvar 42)) ce Ttype todos
      | _ => .failed
