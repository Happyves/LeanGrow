
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrowBeta.Data.Amalgames
import LeanGrowBeta.Utils.Std.List


open Lean Meta


-- # Standard regularisers

def stdRegulariser1 (score : Float) (center span treeScore : Nat) : Float :=
  let factor := max (0.5 : Float) (2 - (1/(Float.ofNat span))*(Float.ofNat (center - treeScore)^2))
  factor * score

def stdRegulariser2 (score : Float) (span treeScore : Nat) : Float :=
  let factor := max (0.5 : Float) (2 - (1/(Float.ofNat span))*(Float.ofNat ( treeScore)^2))
  factor * score



-- # Heights

def updateForwHeight (forwHeights : Array Nat) (ugInds : List Nat) : Array Nat :=
  let rec go (M : Nat) (A : Array Nat) : List Nat → Array Nat
    | [] => A.push (M+1)
    | i :: is =>
        let h := A[i]!
        if h > M
        then go h A is
        else go M A is
  go 0 forwHeights ugInds

def getCandForwHeight (forwHeights : Array Nat) (ugInds : List Nat) : Nat :=
  let rec go (M : Nat) : List Nat → Nat
    | [] => (M+1)
    | i :: is =>
        let h := forwHeights[i]!
        if h > M
        then go h is
        else go M is
  go 0 ugInds

@[inline]
def updateGoalHeight (goalHeights : Array Nat) (spawn_goal_id :  Nat) : Array Nat :=
  let h := goalHeights[spawn_goal_id]! + 1
  goalHeights.push h

@[inline]
def getCandGoalHeight (goalHeights : Array Nat) (spawn_goal_id :  Nat) : Nat :=
  goalHeights[spawn_goal_id]! + 1


-- # Depth

structure depthForwData where
  depth : Nat
  outNei : ListProd Nat Nat
  parents : List Nat
deriving Inhabited, Repr, BEq


private def minimin (m : Nat) : ListProd Nat Nat → Nat
  | .nil => m
  | .cons _ d more => if d < m then minimin d more else minimin m more


partial def updateForwDepth (forwDepths : Array depthForwData) (ugInds : List Nat) : Array depthForwData :=
  let new : depthForwData := ⟨0, .nil, ugInds⟩
  let rec fixNei (origin : Nat) (done : ListProd Nat Nat) : ListProd Nat Nat → ListProd Nat Nat
    | .nil => .cons origin 1 done
    | .cons id D more =>
        if id == origin
        then done.foldl (.cons id (D+1) more) ListProd.cons
        else fixNei origin (.cons id (D+1) done) more
  let rec update (depths : Array depthForwData) : ListProd Nat Nat → Array depthForwData
      | .nil => depths
      | .cons tofix origin more =>
          let ToFix := depths[tofix]!
          let newNei := fixNei origin .nil ToFix.outNei
          match newNei with
          | .nil => panic "[updateForwDepth] shouldn't happen"
          | .cons _ fd _ =>
              let newDep := minimin fd newNei
              if newDep > ToFix.depth
              then
                let nx := ToFix.parents.foldl (fun more p => .cons p tofix more) more
                let rep := {ToFix with depth := newDep, outNei :=  newNei}
                let newDepths := depths.set! tofix rep
                update newDepths nx
              else
                let rep := {ToFix with outNei :=  newNei}
                let newDepths := depths.set! tofix rep
                update newDepths more
  let newGUidx := forwDepths.size
  let init := ugInds.foldl (fun R p => .cons p newGUidx R) .nil
  (update forwDepths init).push new

/-- Minimum among depths of args ; incorporated depth will of course be 0-/
@[inline]
def getCandForwDepth (forwDepths : Array depthForwData) (ugInds : List Nat) : Nat :=
  let ds := ugInds.mapTRR (fun x => forwDepths[x]!.depth)
  let rec mini (m : Nat) : List Nat → Nat
    | [] => m
    | x :: xs => if x < m then mini x xs else mini m xs
  match ds with
  | [] => 0
  | x :: xs => mini x xs

/-
(old) **Note**
In the two function above, we maintain a data structure allowing to find the length of
a shortest path to a sink in the dependecies of gnodes. For each gnode, we maintain
a list of its children, together with the length of a shortest path to a sink for each,
as well a list of its parents. When a node is added, we perform the following loop.
Strating with the parents of the node newly added, we update the parents by increasing
the length of the corresponding child-node by 1, Then, if the minimum length over all
siblings has increased, we enqueue the parents in the loop, since their shortest path
to a sink may have changed. If the minimum didn't change, then length the shortest path of the
parents remains unaffected (though the path may be adifferent one)
-/


structure depthBackData where
  depth : Nat
  outNei : ListProd Nat Nat
  parent : Option Nat
deriving Inhabited, Repr, BEq



partial def updateBackDepth (backDepths : Array depthBackData) (spawn_goal : Nat) : Array depthBackData :=
  let new : depthBackData := ⟨0, .nil, spawn_goal⟩
  let rec fixNei (origin : Nat) (done : ListProd Nat Nat) : ListProd Nat Nat → ListProd Nat Nat
    | .nil => .cons origin 1 done
    | .cons id D more =>
        if id == origin
        then done.foldl (.cons id (D+1) more) ListProd.cons
        else fixNei origin (.cons id (D+1) done) more
  let rec update (depths : Array depthBackData) : ListProd Nat Nat → Array depthBackData
      | .nil => depths
      | .cons tofix origin more =>
          let ToFix := depths[tofix]!
          let newNei := fixNei origin .nil ToFix.outNei
          match newNei with
          | .nil => panic "[updateForwDepth] shouldn't happen"
          | .cons _ fd _ =>
              let newDep := minimin fd newNei
              if newDep > ToFix.depth
              then
                let nx :=
                  match ToFix.parent with
                  | .some P => .cons P tofix more
                  | .none => more
                let rep := {ToFix with depth := newDep, outNei :=  newNei}
                let newDepths := depths.set! tofix rep
                update newDepths nx
              else
                let rep := {ToFix with outNei :=  newNei}
                let newDepths := depths.set! tofix rep
                update newDepths more
  let newGUidx := backDepths.size
  let init := .cons spawn_goal newGUidx .nil
  (update backDepths init).push new


@[inline]
def getCandBackDepth (backDepths : Array depthBackData) (spawn_goal : Nat) : Nat :=
  backDepths[spawn_goal]!.depth
