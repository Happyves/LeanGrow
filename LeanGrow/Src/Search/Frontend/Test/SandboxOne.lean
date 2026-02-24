
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Search.Frontend.Sandbox

import Mathlib.Data.List.Dedup

open List

set_option linter.style.longLine false

-- rws
#check dedup_cons_of_mem'
#check dedup_cons_of_not_mem'
#check length_append
#check dedup_idem
-- rw with propext
#check mem_dedup
-- std
#check dedup_sublist
#check dedup_subset
#check length_erase_le
#check Perm.dedup
-- defs
#check dedup
-- elims
#check_failure List.reverseRecOn -- deprecated ?
-- funinds
#check length.induct

def stdSanbox := #[`List.dedup_cons_of_mem', `List.dedup_cons_of_not_mem', `List.length_append,
  `List.mem_dedup, `List.dedup_idem, `List.dedup_sublist, `List.dedup_subset, `List.length_erase_le, `List.Perm.dedup,
  `List.dedup]

def elimSandbox : Array Lean.Name := #[]

def funIndSandbox := #[`List.length]

#check 1

grow_load_sandbox stdSanbox ; elimSandbox ; funIndSandbox

#check 1

tracing_mode .std
tracing_flags [(`growImpl, TracingFlags.all),
                -- (`searchCore, TracingFlags.all),
                -- (`integrateInduction, TracingFlags.all),
                -- (`integrateBackwardStd, TracingFlags.all),
                -- (`introWiLtxMain, TracingFlags.all),
                -- (`introPass, TracingFlags.all),
                -- (`addForwCandOfStdStep, TracingFlags.all),
                -- (`embedForwInterMain, TracingFlags.all),
                -- (`embedPropaInter, TracingFlags.all),
                ]

-- #exit


#check growImpl

theorem test_0 (l : List Nat) : l.dedup <+ l := by
  grows -- yay

#print test_0

theorem test_0_sol (l : List Nat) : l.dedup <+ l := by
  apply dedup_sublist

#print Sublist

#check Lean.Meta.isExprDefEq

-- #exit


theorem test_1 {α : Type _} [DecidableEq α] (l : List (Nat × α)) : l.dedup <+ l := by
  grows --yay

#print test_1

theorem test_1_sol {α : Type _} [DecidableEq α] (l : List (Nat × α)) : l.dedup <+ l := by
  apply dedup_sublist



theorem test_2 (l : List Nat) : let L := l ++ l ; L.dedup <+ L := by
  grows --yay

#print test_2


theorem test_2_sol (l : List Nat) : let L := l ++ l ; L.dedup <+ L := by
  apply dedup_sublist


-- #exit

theorem test_3 (l : List Nat) : let L := l ++ l ; L.dedup <+ (l ++ l) := by
  grows -- yay
#print test_3


theorem test_3_sol (l : List Nat) : let L := l ++ l ; L.dedup <+ (l ++ l) := by
  apply dedup_sublist


-- #exit

def Even (n : Nat) : Prop := ∃ k, n = 2*k


theorem test_4 (l L : List Nat) (h : Even (l ++ L).length) : Even (l.length + L.length) := by
  grows -- yay

#print test_4

theorem test_4_sol (l L : List Nat) (h : Even (l ++ L).length) : Even (l.length + L.length) := by
  rw [← length_append]
  exact h


-- #exit



theorem test_5 {α : Type _} [DecidableEq α] (l L : List (Nat × α)) (h : Even (l ++ L).length) : Even (l.length + L.length) := by
  grows

#print test_5


theorem test_5_sol {α : Type _} [DecidableEq α] (l L : List (Nat × α)) (h : Even (l ++ L).length) : Even (l.length + L.length) := by
  rw [← length_append]
  exact h


-- #exit

theorem test_6 (l L : List Nat) (h : Even (l.length + L.length)) : let  X := l ++ L ; Even X.length := by
  grows -- yay

#print test_6

theorem test_6_sol (l L : List Nat) (h : Even (l.length + L.length)) : let  X := l ++ L ; Even X.length := by
  dsimp
  rw [length_append]
  exact h


-- tracing_mode .hard
-- tracing_flags [(`growImpl, TracingFlags.all),
--                 (`searchCore, TracingFlags.all),
--                 (`integrateBackwardStd, TracingFlags.all),
--                 (`integrateInduction, TracingFlags.all),
--                 (`introWiLtxMain, TracingFlags.all),
--                 (`introPass, TracingFlags.all),
--                 (`introCore, TracingFlags.all),
--                 (`addThms, TracingFlags.all),
--                 -- (`embedPropaInter, TracingFlags.all),
--                 ]



-- theorem test_7 (l L : List Nat) (P : Nat → Prop) (h : P (l.length + L.length)) : P (l ++ L).length := by
--   grows

-- Currently a memory induced overflow ... (with trace hard, overflow trace stop at different times
-- for different runs ...)

-- #print test_7



theorem test_7_sol (l L : List Nat) (P : Nat → Prop) (h : P (l.length + L.length)) : P (l ++ L).length := by
  rw [length_append]
  exact h


-- #exit



-- theorem test_8 (l : List Nat) (a : Nat) (h : a ∈ l) : a ∈ l.dedup := by
--   grows -- yay
-- overflow ...
-- #print test_8



theorem test_8_sol (l : List Nat) (a : Nat) (h : a ∈ l) : a ∈ l.dedup := by
  rw [mem_dedup]
  exact h


-- #exit

theorem test_9 (l : List Nat) (h : 42 ∈ l) : 42 ∈ l.dedup := by
  grows

#print test_9



theorem test_9_sol (l : List Nat) (h : 42 ∈ l) : 42 ∈ l.dedup := by
  rw [mem_dedup]
  exact h



theorem test_11 (l L : List Nat) (P : List Nat → Prop) (h₁ : l = L) (h₂ : P l) : P L := by
  grows

#print test_11

theorem test_11_sol (l L : List Nat) (P : List Nat → Prop) (h₁ : l = L) (h₂ : P l) : P L := by
  rw [← h₁]
  exact h₂

-- #exit

theorem test_12 (l L : List Nat) (P : List Nat → Prop) (h₀ : 42 = 42) (h₁ : 42 = 42 → l = L) (h₂ : P l) : P L := by
  grows

#print test_12

theorem test_12_sol (l L : List Nat) (P : List Nat → Prop) (h₀ : 42 = 42) (h₁ : 42 = 42 → l = L) (h₂ : P l) : P L := by
  rw [← h₁ h₀]
  exact h₂


-- #exit


-- theorem test_13 (l : List Nat) (P : List Nat → Prop) (h₀ : ∀ a : Nat, a ∈ l.dedup) (h₁ :  P l.dedup) : P (42 :: l).dedup := by
--   grows
-- overflow
-- #print test_13


theorem test_13_sol (l : List Nat) (P : List Nat → Prop) (h₀ : ∀ a : Nat, a ∈ l.dedup) (h₁ :  P l.dedup) : P (42 :: l).dedup := by
  rw [dedup_cons_of_mem']
  · exact h₁
  · apply h₀


-- #exit

@[reducible]
def introable (P : List Nat → Prop) (l : List Nat) :=
  ∀ a, a ∈ l.dedup → P (a :: l).dedup


-- theorem test_15 {l : List Nat} (P : List Nat → Prop) (h₁ : P l.dedup) : introable P l := by
--   grows
-- overflow
-- #print test_15

theorem test_15_sol {l : List Nat} (P : List Nat → Prop) (h₁ : P l.dedup) : introable P l := by
  intro a h₀
  rw [dedup_cons_of_mem']
  · exact h₁
  · exact h₀


-- #exit





-- theorem test_16 (P : List Nat → Prop) (case1 : P [])
--   (case2 : ∀ (head : Nat) (as : List Nat), P as → P (head :: as))
--   (l : List Nat) : P l := by
--     grows
-- [error when printing message: unknown goal [anonymous]]
-- #print test_16


theorem test_16_sol (P : List Nat → Prop) (case1 : P [])
  (case2 : ∀ (head : Nat) (as : List Nat), P as → P (head :: as))
  (l : List Nat) : P l := by
    --apply length.induct
    induction l with
    | nil => apply case1
    | cons x xs ih =>
        apply case2 _ _ ih

-- #exit



-- theorem test_17 (l : List Nat) (a : Nat) (h₁ : a ∈ l)
--   (P : List Nat → Prop) (h₂ : P (a :: l).dedup) : P l.dedup := by
--   grows
-- [error when printing message: unknown goal [anonymous]]
-- #print test_17

theorem test_17_sol (l : List Nat) (a : Nat) (h₁ : a ∈ l)
  (P : List Nat → Prop) (h₂ : P (a :: l).dedup) : P l.dedup := by
   rw [← mem_dedup] at h₁
   rw [dedup_cons_of_mem' h₁] at h₂
   exact h₂

-- #exit


-- theorem test_18 (l : List Nat) (a : Nat) (h₁ : a ∈ l.dedup)
--   : (a :: l).dedup ⊆ l := by
--   grows
-- [error when printing message: unknown goal [anonymous]]
-- #print test_18

theorem test_18_sol (l : List Nat) (a : Nat) (h₁ : a ∈ l.dedup)
  : (a :: l).dedup ⊆ l := by
  rw [dedup_cons_of_mem' h₁]
  apply dedup_subset


-- #exit


-- theorem test_19 (l L : List Nat) (h₁ : 42 ∈ l.dedup) (h₂ : l.dedup ~ L) : (42 :: l).dedup.dedup ~ L.dedup := by
--   grows
-- overflow
-- #print test_19

theorem test_19_sol (l L : List Nat) (h₁ : 42 ∈ l.dedup) (h₂ : l.dedup ~ L) : (42 :: l).dedup.dedup ~ L.dedup := by
  apply Perm.dedup
  rw [dedup_cons_of_mem' h₁]
  exact h₂
