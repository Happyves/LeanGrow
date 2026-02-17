
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Data.Amalgames
import LeanGrow.Src.Utils.Std.List
import LeanGrow.FFI.Lffi


open Lean Meta


-- # Standard regularisers

def stdRegulariser1 (score : Float) (center span treeScore : Nat) : Float :=
  let factor := max (0.5 : Float) (2 - (1/(Float.ofNat span))*(Float.ofNat (center - treeScore)^2))
  factor * score

def stdRegulariser2 (score : Float) (span treeScore : Nat) : Float :=
  let factor := max (0.5 : Float) (2 - (1/(Float.ofNat span))*(Float.ofNat ( treeScore)^2))
  factor * score



-- # Heights

def updateForwHeight (forwHeights : Array Nat) (ugInds : UInt32Array) : Array Nat :=
  let (resM,resA) := ugInds.foldl (Prod.mk 0 forwHeights) (fun i r@(M,A) =>
    let h := A[i.toNat]!
    if h > M
    then (h, A)
    else r
    )
  resA.push resM



def getCandForwHeight (forwHeights : Array Nat) (ugInds : UInt32Array) : Nat :=
  let M := ugInds.foldl 0 (fun i M =>
    let h := forwHeights[i.toNat]!
    if h > M
    then h
    else M
    )
  M+1


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
  parents : UInt32Array
deriving Inhabited, Repr, BEq


private def minimin (m : Nat) : ListProd Nat Nat → Nat
  | .nil => m
  | .cons _ d more => if d < m then minimin d more else minimin m more


partial def updateForwDepth (forwDepths : Array depthForwData) (ugInds : UInt32Array) : Array depthForwData :=
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
                let nx := ToFix.parents.foldl more (fun p more => .cons p.toNat tofix more)
                let rep := {ToFix with depth := newDep, outNei :=  newNei}
                let newDepths := depths.set! tofix rep
                update newDepths nx
              else
                let rep := {ToFix with outNei :=  newNei}
                let newDepths := depths.set! tofix rep
                update newDepths more
  let newGUidx := forwDepths.size
  let init := ugInds.foldl .nil (fun p R => .cons p.toNat newGUidx R)
  (update forwDepths init).push new



/-- Minimum among depths of args ; incorporated depth will of course be 0-/
@[inline]
def getCandForwDepth (forwDepths : Array depthForwData) (ugInds : UInt32Array) : Nat :=
  if ugInds.isEmpty
  then 0
  else
  ugInds.foldl forwDepths[ugInds[0]!.toNat]!.depth (fun x m =>
    let x := forwDepths[x.toNat]!.depth
    if x < m then x else m
    )


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
