/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrowBeta.Search.BackTree.Types
import LeanGrowBeta.Utils.Std.List


open Lean Meta


namespace BackTree

def cleanFails : BackTree → BackTree
  | x@(.fail ..) | x@(.ofUni ..) =>  x
  | .ofGoal pass j t bdirs gdirs ts =>
      let nts := ts.foldl (fun R x => match x with | .fail .. => R | _ => (cleanFails x) :: R) []
      .ofGoal pass j t bdirs gdirs nts
  | .ofPropa pass i j t bdirs gdirs ts =>
      let nts := ts.foldl (fun R x => match x with | .fail .. => R | _ => (cleanFails x) :: R) []
      .ofPropa pass i j t bdirs gdirs nts
  | .ofIntro pass j bvs bdirs gdirs ts =>
      let nts := ts.foldl (fun R x => match x with | .fail .. => R | _ => (cleanFails x) :: R) []
      .ofIntro pass j bvs bdirs gdirs nts
  | .ofBack pass i md  t bdirs gdirs ts =>
      let nts := ts.map cleanFails
      .ofBack pass i md  t bdirs gdirs nts


@[specialize]
partial def modifyAtGoalId
  (goalId : Nat) (modPass : Nat → Nat) (modBdirs modGdirs : List Nat → List Nat) (mod : BackTree → BackTree) (T : BackTree) : BackTree :=
  let rec @[specialize] go : BackTree → BackTree
    | x@(.fail ..) | x@(.ofUni ..) =>  x
    | x@(.ofGoal pass j t bdirs gdirs ts) =>
        if j == goalId
        then mod x
        else
          if !(gdirs.orderedContains goalId)
          then x
          else .ofGoal (modPass pass) j t (modBdirs bdirs) (modGdirs gdirs) (ts.mapTRR go)
    | x@(.ofPropa pass i j t bdirs gdirs ts) =>
        if j == goalId
        then mod x
        else
          if !(gdirs.orderedContains goalId)
          then x
          else .ofPropa (modPass pass) i j t (modBdirs bdirs) (modGdirs gdirs) (ts.mapTRR go)
    | (.ofIntro pass j bvs bdirs gdirs ts) =>
        -- if gdirs.orderedContains goalId
        -- then
        .ofIntro (modPass pass) j bvs (modBdirs bdirs) (modGdirs gdirs) (ts.mapTRR go)
        -- else x
    | x@(.ofBack pass i md n bdirs gdirs ts) =>
        match gdirs.findIdx? (fun l => l.orderedContains goalId) with
        | .none => x
        | .some j =>
            .ofBack (modPass pass) i md n (bdirs.modify j modBdirs) (gdirs.modify j modGdirs) (ts.modify j go)
  go T



@[specialize]
partial def modifyAtBackId
  (backId : Nat) (modPass : Nat → Nat) (modBdirs modGdirs : List Nat → List Nat) (mod : BackTree → BackTree) (T : BackTree) : BackTree :=
  let rec @[specialize] go : BackTree → BackTree
    | x@(.fail ..) | x@(.ofUni ..) =>  x
    | x@(.ofGoal pass j t bdirs gdirs ts) =>
        if !(bdirs.orderedContains backId)
        then x
        else .ofGoal (modPass pass) j t (modBdirs bdirs) (modGdirs gdirs) (ts.mapTRR go)
    | x@(.ofPropa pass i j t bdirs gdirs ts) =>
        if !(bdirs.orderedContains backId)
        then x
        else .ofPropa (modPass pass) i j t (modBdirs bdirs) (modGdirs gdirs) (ts.mapTRR go)
    | x@(.ofIntro pass j bvs bdirs gdirs ts) =>
        if j == backId
        then mod x
        else
          if !(bdirs.orderedContains backId)
          then x
          else  .ofIntro (modPass pass) j bvs (modBdirs bdirs) (modGdirs gdirs) (ts.mapTRR go)
    | x@(.ofBack pass i md n bdirs gdirs ts) =>
        if i == backId
        then mod x
        else
          match bdirs.findIdx? (fun l => l.orderedContains backId) with
          | .none => x
          | .some j =>
              .ofBack (modPass pass) i md n (bdirs.modify j modBdirs) (gdirs.modify j modGdirs) (ts.modify j go)
  go T


@[specialize]
partial def modifyAllDirs
  (modBdirs modGdirs : List Nat → List Nat) (T : BackTree) : BackTree :=
  let rec @[specialize] go : BackTree → BackTree
    | x@(.fail ..) | x@(.ofUni ..) =>  x
    | (.ofGoal pass j t bdirs gdirs ts) =>
        .ofGoal pass j t (modBdirs bdirs) (modGdirs gdirs) (ts.mapTRR go)
    | (.ofPropa pass i j t bdirs gdirs ts) =>
        .ofPropa pass i j t (modBdirs bdirs) (modGdirs gdirs) (ts.mapTRR go)
    | (.ofIntro pass j bvs bdirs gdirs ts) =>
        .ofIntro pass j bvs (modBdirs bdirs) (modGdirs gdirs) (ts.mapTRR go)
    | (.ofBack pass i md n bdirs gdirs ts) =>
        .ofBack pass i md n (bdirs.map modBdirs) (gdirs.map modGdirs) (ts.map go)
  go T

@[specialize]
partial def modifyAllDirsTypes
  (modBdirs modGdirs : List Nat → List Nat) (modType : Expr → Expr) (T : BackTree) : BackTree :=
  let rec @[specialize] go : BackTree → BackTree
    | x@(.fail ..) | x@(.ofUni ..) =>  x
    | (.ofGoal pass j t bdirs gdirs ts) =>
        .ofGoal pass j (modType t) (modBdirs bdirs) (modGdirs gdirs) (ts.mapTRR go)
    | (.ofPropa pass i j t bdirs gdirs ts) =>
        .ofPropa pass i j (modType t) (modBdirs bdirs) (modGdirs gdirs) (ts.mapTRR go)
    | (.ofIntro pass j bvs bdirs gdirs ts) =>
        .ofIntro pass j bvs (modBdirs bdirs) (modGdirs gdirs) (ts.mapTRR go)
    | (.ofBack pass i md n bdirs gdirs ts) =>
        .ofBack pass i md (modType n) (bdirs.map modBdirs) (gdirs.map modGdirs) (ts.map go)
  go T


@[specialize]
partial def addBackstep
  (pass target_goal_id id_gen_goal newbid backArgNum : Nat) (unifIds : List Nat) (backTypes : Array Expr)
  (metadata : BackStepMetadata) (term : Expr) (T : BackTree) : (Nat × BackTree) :=
  let ⟨id_gen_goal, ngds, newB⟩ : Prod3 Nat (List Nat) BackTree := Id.run do
    let mut args : Array BackTree := Array.replicate backArgNum (fail "addBackstep")
    let mut id_gen_goal := id_gen_goal
    let mut ngds := []
    let mut gdirs := Array.replicate backArgNum ([] : List Nat)
    for i in [:backArgNum] do
        let here := BackTree.ofGoal pass id_gen_goal backTypes[i]! [] [] []
        args := args.set! i here
        ngds := id_gen_goal :: ngds
        gdirs := gdirs.set! i [id_gen_goal]
        id_gen_goal := id_gen_goal + 1
    let fill := Array.replicate backArgNum []
    let b := BackTree.ofBack pass newbid metadata term fill gdirs args
    ⟨id_gen_goal, ngds, b⟩
  let Ngds := ngds.reverse
  let ngds := Ngds ++ [id_gen_goal]
  let rec @[specialize] go : BackTree → BackTree
    | x@(.fail ..) | x@(.ofUni ..) =>  x
    | x@(.ofGoal _ j t bdirs gdirs ts) =>
        if j == target_goal_id
        then
            let newB := .ofPropa pass unifIds id_gen_goal t [newbid] Ngds [newB]
            .ofGoal pass j t (bdirs ++ [newbid]) (gdirs ++ ngds) (newB :: ts)
        else
          if !(gdirs.orderedContains target_goal_id)
          then x
          else .ofGoal pass j t (bdirs ++ [newbid]) (gdirs ++ ngds) (ts.mapTRR go)
    | x@(.ofPropa _ i j t bdirs gdirs ts) =>
        if j == target_goal_id
        then
            let newB := .ofPropa pass unifIds id_gen_goal t [newbid] Ngds [newB]
            .ofPropa pass i j t (bdirs ++ [newbid]) (gdirs ++ ngds) (newB :: ts)
        else
          if !(gdirs.orderedContains target_goal_id)
          then x
          else .ofPropa pass i j t (bdirs ++ [newbid]) (gdirs ++ ngds) (ts.mapTRR go)
    | (.ofIntro _ j bvs bdirs gdirs ts) =>
        .ofIntro pass j bvs (bdirs ++ [newbid]) (gdirs ++ ngds) (ts.mapTRR go)
    | x@(.ofBack _ i md n bdirs gdirs ts) =>
        match gdirs.findIdx? (fun l => l.orderedContains target_goal_id) with
        | .none => x
        | .some j =>
            .ofBack pass i md n (bdirs.modify j (fun bdirs => (bdirs ++ [newbid]))) (gdirs.modify j (fun gdirs => (gdirs ++ ngds))) (ts.modify j go)
  let T := go T
  (id_gen_goal, T)



partial def getUnisRequiredFor (targetGoal : Nat) (sofar : List Nat) : List BackTree → List Nat
  | [] => panic s!"[BackTree.getUnisRequiredFor] not finding {targetGoal}"
  | .fail .. :: more |.ofUni .. :: more => getUnisRequiredFor targetGoal sofar more --panic s!"[BackTree.getUnisRequiredFor] arived at leaf without finding {targetGoal}"
  | .ofGoal _ j _ _ gdirs ts :: more =>
      if j == targetGoal
      then sofar
      else
        if gdirs.orderedContains targetGoal
        then getUnisRequiredFor targetGoal sofar (ts ++ more)
        else getUnisRequiredFor targetGoal sofar more -- panic s!"[BackTree.getUnisRequiredFor] not finding {targetGoal}"
  | .ofPropa _ i j _ _ gdirs ts :: more =>
      if j == targetGoal
      then List.orderedUnion sofar i
      else
        if gdirs.orderedContains targetGoal
        then getUnisRequiredFor targetGoal (List.orderedUnion sofar i) (ts ++ more)
        else getUnisRequiredFor targetGoal sofar more --panic s!"[BackTree.getUnisRequiredFor] not finding {targetGoal}"
  | .ofIntro _ _ _ _ gdirs ts :: more =>
      if gdirs.orderedContains targetGoal
      then getUnisRequiredFor targetGoal sofar (ts ++ more)
      else getUnisRequiredFor targetGoal sofar more --panic s!"[BackTree.getUnisRequiredFor] not finding {targetGoal}"
  | .ofBack _ _ _ _ _ gdirs ts :: more =>
        let rec find (i : Nat) : Option BackTree :=
          if i < gdirs.size
          then
            if gdirs[i]!.orderedContains targetGoal
            then ts[i]!
            else find (i+1)
          else
            .none --panic s!"[BackTree.getUnisRequiredFor] not finding {targetGoal} among gdirs {gdirs} at backstep {bid}"
        match find 0 with
        | .some T => getUnisRequiredFor targetGoal sofar (T :: more)
        | .none => getUnisRequiredFor targetGoal sofar more --
