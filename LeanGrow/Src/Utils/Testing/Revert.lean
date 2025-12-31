
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrowBeta.Utils.LeanGrow.TestTools
import LeanGrowBeta.Utils.Lean.Revert

open Lean Meta






def test (n : Name) (cutoff : Nat) : Array Expr → Array Expr → Array Expr → Array Expr → MetaM Unit
  | gs,us,ts, objs => do
      let ficticousGoal := objs[0]!
      let ficticousRevert := #[⟨n⟩]
      let goal ← mkFreshExprMVar (.some ficticousGoal)
      let (_,res) ← goal.mvarId!.revert_NoTn_cutOff (fun _ => true) ficticousRevert cutoff
      let .some assi := (← getMCtx).eAssignment.find? goal.mvarId! | throwError "hmmm"
      IO.println s!"Reverted to {← ppExpr assi} with head of type {← ppExpr (← res.getType)}"


def dummy (n : Nat) (x : Fin n) : Prop := sorry

-- **BUG** cutoff 1 causes overflow
def test1 := test (Name.num `g 0) 2
With gnodes (n : Nat) (hn1 : n = 42) (hn2 : n = 37) (x : Fin n) (hx : x.val = 666) and unodes and tnodes and objects (dummy n x) run test1

def test2 := test (Name.num `g 0) 10
With gnodes (n : Nat) (hn1 : n = 42) (hn2 : n = 37) (x : Fin n) (hx : x.val = 666) and unodes and tnodes and objects (dummy n x) run test2

def test3 := test (Name.num `g 3) 10
With gnodes (n : Nat) (hn1 : n = 42) (hn2 : n = 37) (x : Fin n) (hx : x.val = 666) and unodes and tnodes and objects (dummy n x) run test3

def test4 := test ((Name.num `t 0).num 0) 10
With gnodes (n : Nat) (hn1 : n = 42) (x : Fin n) (hx : x.val = 666) and unodes and tnodes (hn2 : n = 37) and objects (dummy n x) run test4

With gnodes (n : Nat) (hn1 : n = 42) and unodes and tnodes (x : Fin n) (hx : x.val = 666) and objects (dummy n x) run test2
-- semi-negative test ; tnodes don't get reverted, as desired
