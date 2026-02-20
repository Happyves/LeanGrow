

import LeanGrowBeta.Frontend.Sandbox
import Mathlib.Tactic


set_option linter.style.longLine false


#check List.mergeSort
#check List.sorted_mergeSort'
#check List.sorted_mergeSort

def stdSanbox := #[ `Exists.intro, `Or.inl, `Or.inr,
  `List.mergeSort, `List.sorted_mergeSort', `List.sorted_mergeSort,
  ``Nat.mul, `Nat.add, ``Nat.succ, `Nat.zero, ``Nat.succ_eq_add_one, ``Nat.add_zero,
  ``id, ``Eq.refl, ``Nat.le.refl]

def elimSandbox : Array Lean.Name := #[]

def funIndSandbox : Array Lean.Name := #[]

grow_load_sandbox stdSanbox ; elimSandbox ; funIndSandbox

tracing_mode .std
tracing_flags [(`growImpl, TracingFlags.all)]

tracing_flags [(`searchCore, TracingFlags.all),
                --(`integrateBackwardFull, TracingFlags.all),
                -- (`embedBackRWPreIntegrate, TracingFlags.all),--
                -- (`mainBackRW, TracingFlags.all)
                ]
-- #exit

-- theorem test_1 : ∃ f : Nat → Nat, ∀ x, f x = x+1 := by
--   grows
-- #print test_1

-- rw bug

theorem test_1_sol : ∃ f : Nat → Nat, ∀ x, f x = x+1 := by
  use (· + 1) ; intro _ ; rfl

-- #exit

-- theorem test_2 :
--   ∃ f : List Nat → List Nat, ∀ l, List.Sorted (· ≤ ·) (f l) := by
--   grows
-- #print test_2

theorem test_2_sol :
  ∃ f : List Nat → List Nat, ∀ l, List.Sorted (· ≤ ·) (f l) := by
  use List.mergeSort ; intro _ ; apply List.sorted_mergeSort'

-- #exit

-- theorem test_3 : ∃ f : Nat → Nat, ∀ n, f n.succ = n.succ * f n := by
--   grows
-- #print test_3

theorem test_3_sol : ∃ f : Nat → Nat, ∀ n, f n.succ = n.succ * f n := by
  use Nat.factorial ; intro _ ; rfl

theorem test_3_sol_alt : ∃ f : Nat → Nat, ∀ n, f n.succ = n.succ * f n := by
  -- haven't figured out how to refine mvars specifically
  refine ⟨(fun n => @Nat.rec (fun _ => Nat) ?z ?s n),?_⟩
  · exact 1
  · intro m sofar
    exact m.succ*sofar
  · intro n
    dsimp

-- #exit

-- theorem test_4 : ∃ f : Nat → Nat, ∀ n, f n ≤ n := by
--   grows
-- #print test_4

theorem test_4_sol : ∃ f : Nat → Nat, ∀ n, f n ≤ n := by
  use id ; intro _ ; rfl

-- #exit

-- theorem test_5 : ∃ f : Nat → Nat, ∃ n, f n = 0 := by
--   grows
-- #print test_5

theorem test_5_sol : ∃ f : Nat → Nat, ∃ n, f n = 0 := by
  use id ; use 0 ; rfl


-- #exit

-- theorem test_6 (a b c d : Nat)
--   (h₁ : a + b = 42) (h₂ : c + d = 42) (h₃ : a - b = 37) :
--   ∃ x y : Nat, x + y = 42 ∧ x - y = 37 := by
--   grows
-- #print test_6

-- out of fuel ; Exists.intro never gets into best batch

theorem test_6_sol (a b c d : Nat)
  (h₁ : a + b = 42) (h₂ : c + d = 42) (h₃ : a - b = 37) :
  ∃ x y : Nat, x + y = 42 ∧ x - y = 37 := by
  refine ⟨a,b,?_⟩
  constructor <;> assumption

-- #exit

-- theorem test_7 : ∃ n m : Nat, n + m = 42 := by
--   grows
-- #print test_7

-- very curious case of an Eq.refl being applied where it can't ...

theorem test_7_sol : ∃ n m : Nat, n + m = 42 := by
  refine ⟨42,0,?_⟩ ; rfl

-- #exit

-- theorem test_8 (n m : Nat) (f g : Nat → Nat)
--   (hf : ∀ x, f x = n) (hg : ∀ x, g x = m) (hn : Even n) :
--   ∃ f : Nat → Nat, ∀ x, Even (f x) := by
--   grows
-- #print test_8


theorem test_8_sol (n m : Nat) (f g : Nat → Nat)
  (hf : ∀ x, f x = n) (hg : ∀ x, g x = m) (hn : Even n) :
  ∃ f : Nat → Nat, ∀ x, Even (f x) := by
  use f ; intro x ; rwa [hf x]

-- #exit

-- theorem test_9 (x : Nat) : ∃ f : Nat → Nat, f x = x + 1 := by
--   grows
-- #print test_9

-- again the Eq.refl misapplication

theorem test_9_sol (x : Nat) : ∃ f : Nat → Nat, f x = x + 1 := by
  use Nat.succ

theorem test_9_sol_alt (x : Nat) : ∃ f : Nat → Nat, f x = x + 1 := by
  use (fun _ => x+1)

-- #exit

-- theorem test_10 (x : Nat) : ∃ f : Nat → Nat, f x = x + 1 ∧ (∀ y z : Nat, f y = f z) := by
--   grows
-- #print test_10

theorem test_10_sol (x : Nat) : ∃ f : Nat → Nat, f x = x + 1 ∧ (∀ y z : Nat, f y = f z) := by
  use (fun _ => x+1) ; constructor ;
  · rfl
  · intro _ _ ; rfl

--#exit

-- theorem test_11 (x y : Nat) : ∃ f : Nat → Nat, f x = x + 1 ∧ f y = y + 1 := by
--   grows
-- #print test_11

theorem test_11_sol (x y : Nat) : ∃ f : Nat → Nat, f x = x + 1 ∧ f y = y + 1 := by
  use Nat.succ

--#exit

-- theorem test_12 {α : Type} (r : α → α → Prop) (a b c d e : α)
--   (t : ∀ {x y z}, r x y → r y z → r x z)
--   (h1 : r a b) (h2 : r b c) (h3 : r c d) (h4 : r d e) : r a e := by
--   grows
-- #print test_12


theorem test_12_sol {α : Type} (r : α → α → Prop) (a b c d e : α)
  (t : ∀ {x y z}, r x y → r y z → r x z)
  (h1 : r a b) (h2 : r b c) (h3 : r c d) (h4 : r d e) : r a e := by
  exact t (t h1 h2) (t h3 h4)

--#exit

theorem test_13 (a b c d : Prop) (h1 : a ∨ b) (h2 : a → c) (h3 : b → d) : c ∨ d := by
  grows
#print test_13

theorem test_13_sol (a b c d : Prop) (h1 : a ∨ b) (h2 : a → c) (h3 : b → d) : c ∨ d := by
  cases h1 with
  | inl h1 => exact .inl <| h2 h1
  | inr h1 => exact .inr <| h3 h1
