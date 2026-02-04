
/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Utils.LeanGrow.TestTools

open Lean Meta





def test (n : Array Name) (cutoff : Nat) (_ _ _ _ _ _ _ _ _ _ objs : Array Expr) (deps : Array DepCache) (wdeps : Array (FVarId × List FVarId)) : MetaM Unit := do
  let ficticousGoal := objs[0]!
  let ficticousRevert := n.map FVarId.mk
  let ⟨new,res,_,l1,l2⟩ ← revert_NoTn_cutOff_wDepsCache (fun _ => true) (← getLCtx) (← getLocalInstances) ficticousGoal ficticousRevert deps wdeps cutoff
  IO.println s!"Reverted to {← ppExpr new}\nWith term {← ppExpr res}\nOf type {← ppExpr (← InferType res l1 l2)}"


def dummy (n : Nat) (x : Fin n) : Prop := sorry

-- tracing_mode .std
-- tracing_flags [(`revert_NoTn_cutOff_wDepsCache, TracingFlags.all)]

def test1 := test #[(Name.num `g 0)] 10
With context g(n : Nat) g(hn1 : n = 42) g(hn2 : n = 37) g(x : Fin n) g(hx : x.val = 666) and objects (dummy n x) run test1

def test2 := test #[(Name.num `g 0)] 2
With context g(n : Nat) g(hn1 : n = 42) g(hn2 : n = 37) g(x : Fin n) g(hx : x.val = 666) and objects (dummy n x) run test2

def test3 := test #[(Name.num `g 0)] 1
With context g(n : Nat) g(hn1 : n = 42) g(hn2 : n = 37) g(x : Fin n) g(hx : x.val = 666) and objects (dummy n x) run test3

def test4 := test #[(Name.num `g 0)] 0
With context g(n : Nat) g(hn1 : n = 42) g(hn2 : n = 37) g(x : Fin n) g(hx : x.val = 666) and objects (dummy n x) run test4

-- 3 and 4 produce type incorrect terms ; we claim reverting on n only is an abuse
-- in LeanGrow, we should add fvars from the goal that depend on the one we intend to revert
-- to the reverted ones

def test5 := test #[(Name.num `g 0)] 5
With context g(n : Nat) g(hn1 : n = 42) g(hn2 : n = 37) g(x : Fin n) g(hx : x.val = 666) and objects (dummy n x) run test5



def test6 := test #[(Name.num `g 3)] 10
With context g(n : Nat) g(hn1 : n = 42) g(hn2 : n = 37) g(x : Fin n) g(hx : x.val = 666) and objects (dummy n x) run test6

def test7 := test #[(Name.num `g 3)] 2
With context g(n : Nat) g(hn1 : n = 42) g(hn2 : n = 37) g(x : Fin n) g(hx : x.val = 666) and objects (dummy n x) run test7

def test8 := test #[(Name.num `g 3)] 1
With context g(n : Nat) g(hn1 : n = 42) g(hn2 : n = 37) g(x : Fin n) g(hx : x.val = 666) and objects (dummy n x) run test8

def test9 := test #[(Name.num `g 3)] 0
With context g(n : Nat) g(hn1 : n = 42) g(hn2 : n = 37) g(x : Fin n) g(hx : x.val = 666) and objects (dummy n x) run test9





def test10 := test #[(Name.num `g 3), (Name.num `g 0)] 10
With context g(n : Nat) g(hn1 : n = 42) g(hn2 : n = 37) g(x : Fin n) g(hx : x.val = 666) and objects (dummy n x) run test10

def test11 := test #[(Name.num `g 0), (Name.num `g 3)] 10
With context g(n : Nat) g(hn1 : n = 42) g(hn2 : n = 37) g(x : Fin n) g(hx : x.val = 666) and objects (dummy n x) run test11

def test12 := test #[(Name.num `g 3), (Name.num `g 0)] 4
With context g(n : Nat) g(hn1 : n = 42) g(hn2 : n = 37) g(x : Fin n) g(hx : x.val = 666) and objects (dummy n x) run test12

def test13 := test #[(Name.num `g 3), (Name.num `g 0)] 3
With context g(n : Nat) g(hn1 : n = 42) g(hn2 : n = 37) g(x : Fin n) g(hx : x.val = 666) and objects (dummy n x) run test13

def test14 := test #[(Name.num `g 3), (Name.num `g 0)] 2
With context g(n : Nat) g(hn1 : n = 42) g(hn2 : n = 37) g(x : Fin n) g(hx : x.val = 666) and objects (dummy n x) run test14

def test15 := test #[(Name.num `g 3), (Name.num `g 0)] 1
With context g(n : Nat) g(hn1 : n = 42) g(hn2 : n = 37) g(x : Fin n) g(hx : x.val = 666) and objects (dummy n x) run test15

def test16 := test #[(Name.num `g 3), (Name.num `g 0)] 0
With context g(n : Nat) g(hn1 : n = 42) g(hn2 : n = 37) g(x : Fin n) g(hx : x.val = 666) and objects (dummy n x) run test16




def test17 := test #[(Name.num `g 1)] 10
With context g(n : Nat) g(hn1 : n = 42) g(hn2 : n = 37) g(x : Fin n) g(hx : x.val = 666) and objects (dummy n x) run test17

def test18 := test #[(Name.num `g 1)] 1
With context g(n : Nat) g(hn1 : n = 42) g(hn2 : n = 37) g(x : Fin n) g(hx : x.val = 666) and objects (dummy n x) run test18

def test19 := test #[(Name.num `g 1)] 0
With context g(n : Nat) g(hn1 : n = 42) g(hn2 : n = 37) g(x : Fin n) g(hx : x.val = 666) and objects (dummy n x) run test19



def test20 := test #[(Name.num `g 0)] 10
With context g(n : Nat) u(hn1 : n = 42 : (sorry : n = 42)) g(hn2 : n = 37) g(x : Fin n) g(hx : x.val = 666) and objects (dummy n x) run test20

def test21 := test #[(Name.num `g 0)] 2
With context g(n : Nat) u(hn1 : n = 42 : (sorry : n = 42)) g(hn2 : n = 37) g(x : Fin n) g(hx : x.val = 666) and objects (dummy n x) run test21

def test22 := test #[(Name.num `g 0)] 1
With context g(n : Nat) u(hn1 : n = 42 : (sorry : n = 42)) g(hn2 : n = 37) g(x : Fin n) g(hx : x.val = 666) and objects (dummy n x) run test22


def test23 := test #[(Name.num `g 0)] 10
With context g(n : Nat) u(hn1 : n = 42 : (sorry : n = 42)) g(hn2 : n = 37) u(x : Fin n : (⟨0,(sorry : 0 < n)⟩ : Fin n) ) g(hx : x.val = 666) and objects (dummy n x) run test23

def test24 := test #[(Name.num `g 0)] 3
With context g(n : Nat) u(hn1 : n = 42 : (sorry : n = 42)) g(hn2 : n = 37) u(x : Fin n : (⟨0,(sorry : 0 < n)⟩ : Fin n) ) g(hx : x.val = 666) and objects (dummy n x) run test24

def test25 := test #[(Name.num `g 0)] 2
With context g(n : Nat) u(hn1 : n = 42 : (sorry : n = 42)) g(hn2 : n = 37) u(x : Fin n : (⟨0,(sorry : 0 < n)⟩ : Fin n) ) g(hx : x.val = 666) and objects (dummy n x) run test25

def test26 := test #[(Name.num `g 0)] 1
With context g(n : Nat) u(hn1 : n = 42 : (sorry : n = 42)) g(hn2 : n = 37) u(x : Fin n : (⟨0,(sorry : 0 < n)⟩ : Fin n) ) g(hx : x.val = 666) and objects (dummy n x) run test26



def test27 := test #[(Name.num `u 3)] 10
With context g(n : Nat) u(hn1 : n = 42 : (sorry : n = 42)) g(hn2 : n = 37) u(x : Fin n : (⟨0,(sorry : 0 < n)⟩ : Fin n) ) g(hx : x.val = 666) and objects (dummy n x) run test27

def test28 := test #[(Name.num `u 3)] 2
With context g(n : Nat) u(hn1 : n = 42 : (sorry : n = 42)) g(hn2 : n = 37) u(x : Fin n : (⟨0,(sorry : 0 < n)⟩ : Fin n) ) g(hx : x.val = 666) and objects (dummy n x) run test28

def test29 := test #[(Name.num `u 3)] 1
With context g(n : Nat) u(hn1 : n = 42 : (sorry : n = 42)) g(hn2 : n = 37) u(x : Fin n : (⟨0,(sorry : 0 < n)⟩ : Fin n) ) g(hx : x.val = 666) and objects (dummy n x) run test29


def test30 := test #[(Name.num `g 0)] 10
With context g(n : Nat) g(x : Fin n) g(P : Fin n → Prop) g(p : P x) and objects (dummy n x) run test30

def test31 := test #[(Name.num `g 0)] 1
With context g(n : Nat) g(x : Fin n) g(P : Fin n → Prop) g(p : P x) and objects (dummy n x) run test31




def test32 := test #[(Name.num `g 0)] 10
With context g(n : Nat) g(hn1 : n = 42) g(hn2 : n = 37) wg(false : 0 : x : Fin n) wg(false : 1 : hx : x.val = 666) and objects (dummy n x) run test32

def test33 := test #[(Name.num `g 0)] 2
With context g(n : Nat) g(hn1 : n = 42) g(hn2 : n = 37) wg(false : 0 : x : Fin n) wg(false : 1 : hx : x.val = 666) and objects (dummy n x) run test33

def test34 := test #[(Name.num `g 0)] 1
With context g(n : Nat) g(hn1 : n = 42) g(hn2 : n = 37) wg(false : 0 : x : Fin n) wg(false : 1 : hx : x.val = 666) and objects (dummy n x) run test34

def test35 := test #[(Name.num `g 0)] 0
--With context g(n : Nat) g(hn1 : n = 42) g(hn2 : n = 37) wg(false : 0 : x : Fin n) wg(false : 1 : hx : x.val = 666) and objects (dummy n x) run test35


def test36 := test #[(Name.num `u 2)] 10
With context g(n : Nat) g(x : Fin n) u(y : Fin n : x+x) g(P : Fin n → Prop) and objects (P y) run test36


def test37 := test #[(Name.num `g 1)] 10
With context g(n : Nat) g(x : Fin n) u(y : Fin n : x+x) g(P : Fin n → Prop) and objects (P y) run test37

def test38 := test #[(Name.num `u 2),(Name.num `g 1)] 10
With context g(n : Nat) g(x : Fin n) u(y : Fin n : x+x) g(P : Fin n → Prop) and objects (P y) run test38

-- tracing_mode .std
-- tracing_flags [(`revert_NoTn_cutOff_wDepsCache, TracingFlags.all),
--                 (`Lean.Expr.abstractLetFvarAll_proofLet, TracingFlags.all)]


def test39 := test #[(Name.num `u 3),(Name.num `g 1)] 10
With context g(n : Nat) g(x : Fin (n+1)) g(P : (k : Nat) → Fin k → Prop) u(y : Fin (n+1) : x+x) and objects (∀ t : y.val + 1 < n+1, P (n+1) ⟨y.val + 1, t⟩) run test39
