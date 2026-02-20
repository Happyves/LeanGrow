
import LeanGrowBeta.Frontend.Sandbox
import Mathlib.Tactic

open List

set_option linter.style.longLine false


#check List.getElem_filter
#check List.getElem_append_left
#check List.getElem_append_right
#check List.getElem_of_eq
#check List.getElem_range
#check List.getElem_cons
#check List.getElem_cons_succ
#check List.getElem_cons_zero
#check List.getElem_map
#check List.length_append
#check List.length_map
#check dif_neg
#check dif_pos


def stdSanbox := #[`List.getElem_filter, `List.getElem_append_left, `List.getElem_append_right,
  `List.getElem_of_eq, `List.getElem_range, `List.getElem_cons, `List.getElem_cons_succ, `List.getElem_cons_zero, `List.getElem_map,
  `Eq.refl, `List.length_append, `List.length_map, `dif_neg, `dif_pos]

def elimSandbox : Array Lean.Name := #[]

def funIndSandbox : Array Lean.Name := #[]

grow_load_sandbox stdSanbox ; elimSandbox ; funIndSandbox

tracing_mode .std --.hard
tracing_flags [(`growImpl, TracingFlags.all)]

-- #exit

tracing_flags [(`searchCore, TracingFlags.all),
                --(`integrateBackwardFull, TracingFlags.all),
                -- (`embedBackRWPreIntegrate, TracingFlags.all),--
                -- (`mainBackRW, TracingFlags.all)
                ]

-- set_option pp.all true

-- theorem test_1 (l L : List Nat) (i : Nat)
--   (h₁ : i < (l ++ L ++ l).length) (h₂ : i < (l ++ L).length) (h₃ : l.length ≤ i) :
--   (l ++ L ++ l)[i] = L[i - l.length]'(by rw [length_append] at h₂; exact Nat.sub_lt_left_of_lt_add h₃ h₂) := by
--   grows
-- #print test_1
-- takes around 40 sec, ends in a failure caused by rewriting

theorem test_1_sol (l L : List Nat) (i : Nat)
  (h₁ : i < (l ++ L ++ l).length) (h₂ : i < (l ++ L).length) (h₃ : l.length ≤ i) :
  (l ++ L ++ l)[i] = L[i - l.length]'(by rw [length_append] at h₂; exact Nat.sub_lt_left_of_lt_add h₃ h₂) := by
  rw [List.getElem_append_left h₂]
  rw [List.getElem_append_right h₃]

#check List.getElem_append

-- length_map
-- failure in rw it seems
#check List.get
#print instGetElemNatLtLength


-- #exit

-- theorem test_2 {α : Type _} {l : List α} {i j : Nat} (h : i = j) (w : i < l.length) : l[i] = l[j] := by
--   grows
-- #print test_2


theorem test_2_sol {α : Type _} {l : List α} {i j : Nat} (h : i = j) (w : i < l.length) : l[i] = l[j] := by
  --rw [h] -- motive not type correct
  generalize_proofs W
  revert W
  rw [← h]
  intro _
  rfl

-- #exit

-- theorem test_3 {α β : Type _} (f : α → β) {l : List α} {i : Nat} {h : i < l.length} :
--   (map f l)[i]'(by rwa [length_map]) = f l[i] := by
--   grows
-- #print test_3
-- ends in whnf timeout
-- **Bug** `getElem_map` is used, but subgoal isn't unified
-- and rewritten goal is the same ...


theorem test_3_sol {α β : Type _} (f : α → β) {l : List α} {i : Nat} {h : i < l.length} :
  (map f l)[i]'(by rwa [length_map]) = f l[i] := by
  apply getElem_map

-- #exit

-- theorem test_4 {l : List Nat} {i : Nat} {h : i < l.length} :
--   (map (fun x => x^2) l)[i]'(by rwa [length_map]) = l[i]^2 := by
--   grows
-- #print test_4


theorem test_4_sol {l : List Nat} {i : Nat} {h : i < l.length} :
  (map (fun x => x^2) l)[i]'(by rwa [length_map]) = l[i]^2 := by
  apply getElem_map


-- #exit

-- theorem test_5 {α : Type _} {i : Nat} {a : α} {l : List α} (w : i < (a :: l).length)
--   (h : i ≠ 0) : (a :: l)[i] = l[i - 1]'(match i, h with | i+1, _ => Nat.succ_lt_succ_iff.mp w) := by
--   grows
-- #print test_5



theorem test_5_sol {α : Type _} {i : Nat} {a : α} {l : List α} (w : i < (a :: l).length)
  (h : i ≠ 0) : (a :: l)[i] = l[i - 1]'(match i, h with | i+1, _ => Nat.succ_lt_succ_iff.mp w) := by
  rw [getElem_cons]
  rw [dif_neg h]

-- #exit

-- theorem test_6 : [1,2,3,4,5][1] = 1+1 := by
--   grows
-- #print test_6


theorem test_6_sol : [1,2,3,4,5][1] = 1+1 := by rfl

-- #exit

-- theorem test_7 : (List.range 6)[2] = 1+1 := by
--   grows
-- #print test_7


theorem test_7_sol : (List.range 6)[2] = 1+1 := by rfl


#check List.Pairwise
#check Int.le_add_one
#check Int.add_le_add
