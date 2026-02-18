/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Search.BackTree.Types
import LeanGrow.Src.Utils.Std.List


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
  (goalId : Nat) (modPass : Nat → Nat) (modBdirs modGdirs : UInt32Array → UInt32Array) (mod : BackTree → BackTree) (T : BackTree) : BackTree :=
  let rec @[specialize] go : BackTree → BackTree
    | x@(.fail ..) | x@(.ofUni ..) =>  x
    | x@(.ofGoal pass j t bdirs gdirs ts) =>
        if j == goalId
        then mod x
        else
          if !(gdirs.oContains goalId.toUInt32)
          then x
          else .ofGoal (modPass pass) j t (modBdirs bdirs) (modGdirs gdirs) (ts.mapTRR go)
    | x@(.ofPropa pass i j t bdirs gdirs ts) =>
        if j == goalId
        then mod x
        else
          if !(gdirs.oContains goalId.toUInt32)
          then x
          else .ofPropa (modPass pass) i j t (modBdirs bdirs) (modGdirs gdirs) (ts.mapTRR go)
    | (.ofIntro pass j bvs bdirs gdirs ts) =>
        -- if gdirs.orderedContains goalId
        -- then
        .ofIntro (modPass pass) j bvs (modBdirs bdirs) (modGdirs gdirs) (ts.mapTRR go)
        -- else x
    | x@(.ofBack pass i md n bdirs gdirs ts) =>
        match gdirs.findIdx? (fun l => l.oContains goalId.toUInt32) with
        | .none => x
        | .some j =>
            .ofBack (modPass pass) i md n (bdirs.modify j modBdirs) (gdirs.modify j modGdirs) (ts.modify j go)
  go T



@[specialize]
partial def modifyAtBackId
  (backId : Nat) (modPass : Nat → Nat) (modBdirs modGdirs : UInt32Array → UInt32Array) (mod : BackTree → BackTree) (T : BackTree) : BackTree :=
  let rec @[specialize] go : BackTree → BackTree
    | x@(.fail ..) | x@(.ofUni ..) =>  x
    | x@(.ofGoal pass j t bdirs gdirs ts) =>
        if !(bdirs.oContains backId.toUInt32)
        then x
        else .ofGoal (modPass pass) j t (modBdirs bdirs) (modGdirs gdirs) (ts.mapTRR go)
    | x@(.ofPropa pass i j t bdirs gdirs ts) =>
        if !(bdirs.oContains backId.toUInt32)
        then x
        else .ofPropa (modPass pass) i j t (modBdirs bdirs) (modGdirs gdirs) (ts.mapTRR go)
    | x@(.ofIntro pass j bvs bdirs gdirs ts) =>
        if j == backId
        then mod x
        else
          if !(bdirs.oContains backId.toUInt32)
          then x
          else  .ofIntro (modPass pass) j bvs (modBdirs bdirs) (modGdirs gdirs) (ts.mapTRR go)
    | x@(.ofBack pass i md n bdirs gdirs ts) =>
        if i == backId
        then mod x
        else
          match bdirs.findIdx? (fun l => l.oContains backId.toUInt32) with
          | .none => x
          | .some j =>
              .ofBack (modPass pass) i md n (bdirs.modify j modBdirs) (gdirs.modify j modGdirs) (ts.modify j go)
  go T



@[specialize]
partial def modifyAllDirs
  (modBdirs modGdirs : UInt32Array → UInt32Array) (T : BackTree) : BackTree :=
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
  (modBdirs modGdirs : UInt32Array → UInt32Array) (modType : Expr → Expr) (T : BackTree) : BackTree :=
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
  (pass target_goal_id id_gen_goal newbid backArgNum : Nat) (unifIds : UInt32Array) (backTypes : Array Expr)
  (metadata : BackStepMetadata) (term : Expr) (T : BackTree) : (Nat × BackTree) :=
  let ⟨id_gen_goal, ngds, newB⟩ : Prod3 Nat (UInt32Array) BackTree := Id.run do
    let mut args : Array BackTree := Array.replicate backArgNum (fail "addBackstep")
    let mut id_gen_goal := id_gen_goal
    let mut ngds := (.empty : UInt32Array)
    let mut gdirs := Array.replicate backArgNum (.empty : UInt32Array)
    for i in [:backArgNum] do
        let here := BackTree.ofGoal pass id_gen_goal backTypes[i]! .empty .empty []
        args := args.set! i here
        ngds := ngds.push id_gen_goal.toUInt32
        gdirs := gdirs.set! i (.single id_gen_goal.toUInt32)
        id_gen_goal := id_gen_goal + 1
    let fill := Array.replicate backArgNum (.empty : UInt32Array)
    let b := BackTree.ofBack pass newbid metadata term fill gdirs args
    ⟨id_gen_goal, ngds, b⟩
  let Ngds := ngds
  let ngds := ngds.push id_gen_goal.toUInt32
  let rec @[specialize] go : BackTree → BackTree
    | x@(.fail ..) | x@(.ofUni ..) =>  x
    | x@(.ofGoal _ j t bdirs gdirs ts) =>
        if j == target_goal_id
        then
            let newB := .ofPropa pass unifIds id_gen_goal t (.single newbid.toUInt32) Ngds [newB]
            .ofGoal pass j t (bdirs.push newbid.toUInt32) (.union gdirs ngds) (newB :: ts)
        else
          if !(gdirs.oContains target_goal_id.toUInt32)
          then x
          else .ofGoal pass j t (bdirs.push newbid.toUInt32) (.union gdirs ngds) (ts.mapTRR go)
    | x@(.ofPropa _ i j t bdirs gdirs ts) =>
        if j == target_goal_id
        then
            let newB := .ofPropa pass unifIds id_gen_goal t (.single newbid.toUInt32) Ngds [newB]
            .ofPropa pass i j t (bdirs.push newbid.toUInt32) (.union gdirs ngds) (newB :: ts)
        else
          if !(gdirs.oContains target_goal_id.toUInt32)
          then x
          else .ofPropa pass i j t (bdirs.push newbid.toUInt32) (.union gdirs ngds) (ts.mapTRR go)
    | (.ofIntro _ j bvs bdirs gdirs ts) =>
        .ofIntro pass j bvs (bdirs.push newbid.toUInt32) (.union gdirs ngds) (ts.mapTRR go)
    | x@(.ofBack _ i md n bdirs gdirs ts) =>
        match gdirs.findIdx? (fun l => l.oContains target_goal_id.toUInt32) with
        | .none => x
        | .some j =>
            .ofBack pass i md n (bdirs.modify j (fun bdirs => (bdirs.push newbid.toUInt32))) (gdirs.modify j (fun gdirs => (.union gdirs ngds))) (ts.modify j go)
  let T := go T
  (id_gen_goal, T)



partial def getUnisRequiredFor (targetGoal : Nat) (sofar : UInt32Array) : List BackTree → UInt32Array
  | [] => panic s!"[BackTree.getUnisRequiredFor] not finding {targetGoal}"
  | .fail .. :: more |.ofUni .. :: more => getUnisRequiredFor targetGoal sofar more --panic s!"[BackTree.getUnisRequiredFor] arived at leaf without finding {targetGoal}"
  | .ofGoal _ j _ _ gdirs ts :: more =>
      if j == targetGoal
      then sofar
      else
        if gdirs.oContains targetGoal.toUInt32
        then getUnisRequiredFor targetGoal sofar (ts ++ more)
        else getUnisRequiredFor targetGoal sofar more -- panic s!"[BackTree.getUnisRequiredFor] not finding {targetGoal}"
  | .ofPropa _ i j _ _ gdirs ts :: more =>
      if j == targetGoal
      then .union sofar i
      else
        if gdirs.oContains targetGoal.toUInt32
        then getUnisRequiredFor targetGoal (.union sofar i) (ts ++ more)
        else getUnisRequiredFor targetGoal sofar more --panic s!"[BackTree.getUnisRequiredFor] not finding {targetGoal}"
  | .ofIntro _ _ _ _ gdirs ts :: more =>
      if gdirs.oContains targetGoal.toUInt32
      then getUnisRequiredFor targetGoal sofar (ts ++ more)
      else getUnisRequiredFor targetGoal sofar more --panic s!"[BackTree.getUnisRequiredFor] not finding {targetGoal}"
  | .ofBack _ _ _ _ _ gdirs ts :: more =>
        let rec find (i : Nat) : Option BackTree :=
          if i < gdirs.size
          then
            if gdirs[i]!.oContains targetGoal.toUInt32
            then ts[i]!
            else find (i+1)
          else
            .none --panic s!"[BackTree.getUnisRequiredFor] not finding {targetGoal} among gdirs {gdirs} at backstep {bid}"
        match find 0 with
        | .some T => getUnisRequiredFor targetGoal sofar (T :: more)
        | .none => getUnisRequiredFor targetGoal sofar more --
