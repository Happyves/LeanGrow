
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Batteries.Tactic.OpenPrivate
import Lean.Meta.Tactic.Grind.RevertAll
import LeanGrow.Src.Utils.Lean.Expr.Basic

open Lean Meta

-- **Note** the code is based on:
#check MVarId.revert



@[specialize]
def List.takeWhileCounting (p : α → Bool) (c max : Nat) (done : List α) : (xs : List α) → List α
  | [] => done
  | hd :: tl =>
    if c < max
    then
      match p hd with
      | true  => takeWhileCounting p (c+1) max (hd :: done) tl
      | false => takeWhileCounting p c max done tl
    else
      done

@[specialize]
def List.takeWhileCountingM (p : α → MetaM Bool) (c max : Nat) (done : List α) : (xs : List α) → MetaM (List α)
  | [] => return done
  | hd :: tl => do
    if c < max
    then
      match ← p hd with
      | true  => takeWhileCountingM p (c+1) max (hd :: done) tl
      | false => takeWhileCountingM p c max done tl
    else
      return done


@[specialize]
partial def Lean.MVarId.revert_NoTn_cutOff_wDepsCache (introAdmissible? : Nat → Bool)
  (l1 : LocalContext) (l2 : LocalInstances)
  (goal : Expr) (guFvs : Array FVarId)
  (depsCache : Array (Prod3 Bool (List FVarId) (List FVarId)))
  (workerDepsCache : Array (FVarId × (List FVarId))) (RevCutOff : Nat)
  : MetaM (Prod3 MVarId Expr (Array FVarId)) :=
  let spread := RevCutOff / guFvs.size
  let rec @[specialize] augment (track : UInt32Array) (final : Array FVarId) (pass : List FVarId) (next : List (List FVarId)) : UInt32Array × Array FVarId :=
    if final.size < RevCutOff
    then
      match pass with
      | [] =>
        match next with
        | [] =>
            let res := final.qsort (fun x y =>
              match x.name, y.name with
              | .num _ i, .num _ j => i < j -- increase in dependence ; qsort expects strict order
              | _, _ => panic s!"[revert_NoTn_cutOff_wDepsCache][augment] unexpected formats {x.name} {y.name}")
            (track, res)
        | f :: fs => augment track final f fs
      | nx :: more =>
        match nx.name with
        | .num _ i =>
            let I := i.toUInt32
            if track.oContains I
            then augment track final more next
            else
              let lD := depsCache[i]!.snd.takeWhileCounting (fun x =>
                match x.name with
                | .num _ i => introAdmissible? i
                | _ => panic s!"[revert_NoTn_cutOff_wDepsCache][augment] unexpected formats {x.name}"
                ) 0 spread []
              augment (track.oInsert I) (final.push nx) more (next ++ [lD]) -- add to back
        | _ =>
             panic s!"[revert_NoTn_cutOff_wDepsCache][augment] unexpected formats {nx.name}"
    else
      let res := final.qsort (fun x y =>
        match x.name, y.name with
        | .num _ i, .num _ j => i < j -- increase in dependence ; qsort expects strict order
        | _, _ => panic s!"[revert_NoTn_cutOff_wDepsCache][augment] unexpected formats {x.name} {y.name}")
      (track, res)

  sorry
/-
  - filter backdeps on whether they depend on final, in close
  - to depermine this, make a version of `getWorkerIndsTransR` but à la check exists, but where we use depsCache, and where we seek a transitive dep in final
  - in close, use an UInt32Array to keep track of independent one, so that we may skip them when occuing multiple times

-/

#exit
  let rec close (track : UInt32Array) (final : Array FVarId) (idx : Nat) (pass : List FVarId) : Array FVarId :=
    match pass with
    | [] =>
      let idx := idx+1
      if idx >= final.size
      then final
      else
        let nx := final[idx]!
        match nx.name with
        | .num _ i =>
            let D := depsCache[i]!.thd
            -- HERE
            close track final idx D
        | _ =>
            panic s!"[revert_NoTn_cutOff_wDepsCache][close] unexpected formats {nx.name}"
    | nx :: more =>
      let seen := final.binSearchContains nx (fun x y =>
        match x.name, y.name with
        | .num _ i, .num _ j => i < j -- expects strict order
        | _, _ => panic s!"[revert_NoTn_cutOff_wDepsCache][close] unexpected formats {x.name} {y.name}"
        ) 0 idx
      if seen -- backward dependence must have smaller index, so it suffices to search in [0,idx]
      then close track final idx more
      else
        match nx.name with
        | .num _ i =>
            let D := depsCache[i]!.thd
            let final := final.binInsert (fun x y =>
              match x.name, y.name with
              | .num _ i, .num _ j => i < j -- expects strict order
              | _, _ => panic s!"[revert_NoTn_cutOff_wDepsCache][close] unexpected formats {x.name} {y.name}"
              ) nx
            close track final (idx+1) (D ++ more)
        | _ =>
            panic s!"[revert_NoTn_cutOff_wDepsCache][close] unexpected formats {nx.name}"
  let rec @[specialize] mkRevs : Array FVarId :=
    if spread == 0
    then
      let res := guFvs.qsort (fun x y =>
        match x.name, y.name with
        | .num _ i, .num _ j => i < j -- increase in dependence ; qsort expects strict order
        | _, _ => panic s!"[revert_NoTn_cutOff_wDepsCache][mkRevs] unexpected formats {x.name} {y.name}")
      let track : UInt32Array :=
        res.foldl (fun A nx =>
          match nx.name with
          | .num _ i =>
              A.push i.toUInt32
          | _ =>
              panic s!"[revert_NoTn_cutOff_wDepsCache][mkRevs] unexpected formats {nx.name}"
          ) (.emptyWithCapacity res.size)
      let ini := res[0]!
      match ini.name with
      | .num _ i =>
          let pass := depsCache[i]!.thd
          close track res 0 pass
      | _ =>
          panic s!"[revert_NoTn_cutOff_wDepsCache][mkRevs] unexpected formats {ini.name}"
    else
      let (track,res) := augment (.emptyWithCapacity RevCutOff) (.emptyWithCapacity RevCutOff) guFvs.toList []
      let ini := res[0]!
      match ini.name with
        | .num _ i =>
            let pass := depsCache[i]!.thd
            close track res 0 pass
        | _ =>
            panic s!"[revert_NoTn_cutOff_wDepsCache][mkRevs] unexpected formats {ini.name}"
  -- todo : workerDepsCache ; new goal, rervert-term ; proof-valed-lets to ∀s
  sorry
