
import LeanGrowBeta.Frontend.Sandbox
import Mathlib.Tactic


set_option linter.style.longLine false


#check List.length_append


def stdSanbox := #[`List.length_append]

def elimSandbox : Array Lean.Name := #[]

def funIndSandbox : Array Lean.Name := #[]

-- grow_load_sandbox stdSanbox ; elimSandbox ; funIndSandbox

tracing_mode .std
tracing_flags [(`growImpl, TracingFlags.all)]


-- #exit


theorem test_1 (x y : Int) : x^2 + x*(y+1) = y*x + x*(x+1) := by
  sorry
#print test_1

theorem test_1_sol (x y : Int) : x^2 + x*(y+1) = y*x + x*(x+1) := by ring

--#exit

theorem test_2 (x y : Int) (h₁ : x - y ≤ 3) (h₂ : x + y ≤ 2) : 2*x ≤ 5 := by
  sorry
#print test_2

theorem test_2_sol (x y : Int) (h₁ : x - y ≤ 3) (h₂ : x + y ≤ 2) : 2*x ≤ 5 := by linarith

--#exit


theorem test_3 (l L : List Int) : ((l ++ L).length)^2 + l.length^2 = L.length*(2*l.length + L.length) + 2*l.length^2 := by
  sorry
#print test_3

theorem test_3_sol (l L : List Int) : ((l ++ L).length)^2 + l.length^2 = L.length*(2*l.length + L.length) + 2*l.length^2 := by
  rw [List.length_append]
  ring

--#exit

theorem test_4 (l L : List Int) (h₁ : (l ++ L).length ≠ 0) (h₂ : l.length + L.length = 0) : l = L := by
  sorry
#print test_4

theorem test_4_sol (l L : List Int) (h₁ : (l ++ L).length ≠ 0) (h₂ : l.length + L.length = 0) : l = L := by
  rw [List.length_append] at h₁
  absurd h₂
  exact h₁
#print test_4_sol


--#exit

theorem test_5 (l : List Nat) {x : Nat} (h : l = .cons x l) : False := by
  sorry
#print test_5

theorem test_5_sol (l : List Nat) {x : Nat} (h : l = .cons x l) : False := by
  induction' l with a as ih
  · contradiction
  · have := List.cons.inj h
    rw [← this.2] at h
    exact ih h

--#exit

theorem test_6 (l : List Nat) {x : Nat} (h : [] = .cons x l) : False := by
  sorry
#print test_6

theorem test_6_sol (l : List Nat) {x : Nat} (h : [] = .cons x l) : False := by
  contradiction
#print test_6_sol

--#exit

theorem test_7 {x : Nat} (h : x.succ ≤ 0) : False := by
  sorry
#print test_7

theorem test_7_sol {x : Nat} (h : x.succ ≤ 0) : False := by
  contradiction
#print test_7_sol

--#exit

theorem test_8 {x : Nat} (h : x = 42) (b : ∀ y, y = 42 → False) : x = x+1 := by
  sorry
#print test_8

theorem test_8_sol {x : Nat} (h : x = 42) (b : ∀ y, y = 42 → False) : x = x+1 := by
  exfalso
  exact b x h


--#exit

theorem test_9 (l L t T : List Nat) (h : l ++ L = t ++ T)
  (P : List Nat → List Nat → Nat) : P l ((l ++ L) ++ t) = P l ((t ++ T) ++ t) := by
  sorry
#print test_9

theorem test_9_sol (l L t T : List Nat) (h : l ++ L = t ++ T)
  (P : List Nat → List Nat → Nat) : P l ((l ++ L) ++ t) = P l ((t ++ T) ++ t) := by
  congr

--#exit

theorem test_10 (a b c d : Nat) (h₁ : a = b) (h₂ : c = d) : a + c = b + d := by
  sorry
#print test_10

theorem test_10_sol (a b c d : Nat) (h₁ : a = b) (h₂ : c = d) : a + c = b + d := by
  grind
  -- cc is deprecated
