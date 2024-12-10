
import Qq
import Lean
import Mathlib.Tactic

import Mathlib.Algebra.Group.Defs

#check 1

open Qq

#eval q(List.append [1,2])

#eval q(@add_comm Rat)
#eval q(@add_comm (List Type))
#eval q(Rat)

open Lean

#check ConstantInfo


def test (n : Name) : CoreM Unit := do
  let env ← getEnv
  let data := env.constants.find! n
  IO.print s!"{repr data.type}"

#eval test `add_comm

#eval test `Rat

def add_comm_spe := @add_comm ℤ

def test' (n : Name) : CoreM Unit := do
  let env ← getEnv
  let data := env.constants.find! n
  IO.print s!"{repr data.value!}"

#eval test' `add_comm_spe


def testin (a b : Nat) (P : Nat → Prop) (eq : a = b) (h : P a) : P b :=
  by
  rw [← eq]
  exact h

#eval test' `testin

#check congrArg
#check congr
#check Eq.mpr

def testin' (a b : Nat) (P : Nat → Prop) (eq : a = b) (h : P a) : P b :=
  by
  simp_rw [← eq]
  exact h

#eval test' `testin'


def testin2 (a b : Nat) (P : Nat → Prop) (h : P (a+b)) : P (b+a) :=
  by
  rw [add_comm]
  exact h

#eval test' `testin2

open Meta

def test2 (n : Name) : MetaM Unit := do
  let env ← getEnv
  let data := env.constants.find! n
  let cleaned ← reduce data.value! false false false
  IO.print s!"{repr (cleaned)}"

#eval test2 `testin2
#eval test2 `testin


#check Eq.rec


def testin3 (a b : Nat) (P : Nat → Prop) (Q : Prop) (h : P (a+b)) (H : P (b+a) → Q) : Q :=
  by
  rw [add_comm] at h
  exact H h

#eval test' `testin3

def testin4 (a b : Nat) (P : Nat → Prop) (Q : Prop) (h : P (a+b)) (H : P (b+a) → Q) : Q :=
  by
  apply H
  convert h using 1
  apply add_comm

#eval test' `testin4
