

import Lean

import Std.Tactic.Do
import Batteries.Control.LawfulMonadState
import Mathlib.Control.Lawful
import Batteries.Control.ForInStep

open Std.Do

open Lean Meta


#check PostShape
-- PostCond.lean depends on SPred

#check PredTrans.Monotonic
-- PredTrans.lean depends on PostCond



#check bind_pure
-- Init

#check monadStateOf_get_eq_get
-- Batteries


#check StateT.run_mk
-- Mathlib


def mySum' (l : List Nat) : Nat := Id.run do
  let mut out := 0
  for i in l do
    out := out + i
  return out

theorem mySum_correct_vanilla (l : List Nat) : mySum' l = l.sum := by
  unfold mySum'
  dsimp
  have :
    (forIn l 0 fun i r => do
      pure PUnit.unit
      pure (ForInStep.yield (r + i)) : Id _).run =
    (forIn l 0 fun i r => do
      pure (ForInStep.yield (r + i)) : Id _).run := by
        --congr -- closes goal
        apply congrArg
        apply congrArg
        funext i r
        rw [pure_bind PUnit.unit]
  rw [this]
  clear this
  rw [List.forIn_pure_yield_eq_foldl]
  rw [Id.run_pure]
  rw [List.sum]
  sorry -- why foldr



  --rw [List.forIn_pure_yield_eq_foldl]

#check bind_pure_comp
#check map_pure
#check Array.forIn_pure_yield_eq_foldl
#check List.size_toArray
#check List.foldl_toArray'
#check bind_pure
#check Id.run_pure
#check List.sum_toArray

#check List.forIn_pure_yield_eq_foldl

#check pure_bind
#check List.foldl_eq_foldr_reverse


#exit

-- # From tutorial

def mySum (l : Array Nat) : Nat := Id.run do
  let mut out := 0
  for i in l do
    out := out + i
  return out

theorem mySum_correct (l : Array Nat) : mySum l = l.sum := by
  -- Focus on the part of the program with the `do` block (`Id.run ...`)
  generalize h : mySum l = x
  apply Id.of_wp_run_eq h
  -- Break down into verification conditions
  mvcgen
  -- Specify the invariant which should hold throughout the loop
  -- * `out` refers to the current value of the `let mut` variable
  -- * `xs` is a `List.Cursor`, which is a data structure representing
  --   a list that is split into `xs.prefix` and `xs.suffix`.
  --   It tracks how far into the loop we have gotten.
  -- Our invariant is that `out` holds the sum of the prefix.
  -- The notation ⌜p⌝ embeds a `p : Prop` into the assertion language.
  case inv1 => exact ⇓⟨xs, out⟩ => ⌜xs.prefix.sum = out⌝
  -- After specifying the invariant, we can further simplify our goals
  -- by "leaving the proof mode". `mleave` is just
  -- `simp only [...] at *` with a stable simp subset.
  all_goals mleave
  -- Prove that our invariant is preserved at each step of the loop
  case vc1 ih =>
    -- The goal here mentions `pref`, which binds the `prefix` field of
    -- the cursor passed to the invariant. Unpacking the
    -- (dependently-typed) cursor makes it easier for `grind`.
    grind
  -- Prove that the invariant is true at the start
  case vc2 =>
    grind
  -- Prove that the invariant at the end of the loop implies the
  -- property we wanted
  case vc3 h =>
    grind


theorem mySum_correct_vanilla (l : Array Nat) : mySum l = l.sum := by
  -- Turn the array into a list
  cases l with | mk l =>
  -- Unfold `mySum` and rewrite `forIn` to `foldl`
  simp only [mySum, bind_pure_comp, map_pure, Array.forIn_pure_yield_eq_foldl, List.size_toArray,
    List.foldl_toArray', bind_pure, Id.run_pure, List.sum_toArray]
  -- Generalize the inductive hypothesis
  suffices h : ∀ out, List.foldl (· + ·) out l = out + l.sum by simp [h]
  -- Grind away
  induction l with grind


def nodup (l : List Int) : Bool := Id.run do
  let mut seen : Std.HashSet Int := ∅
  for x in l do
    if x ∈ seen then
      return false
    seen := seen.insert x
  return true


theorem nodup_correct (l : List Int) : nodup l ↔ l.Nodup := by
  generalize h : nodup l = r
  apply Id.of_wp_run_eq h
  mvcgen
  invariants
  · Invariant.withEarlyReturn
      (onReturn := fun ret seen => ⌜ret = false ∧ ¬l.Nodup⌝)
      (onContinue := fun xs seen =>
        ⌜(∀ x, x ∈ seen ↔ x ∈ xs.prefix) ∧ xs.prefix.Nodup⌝)
  with grind


structure Supply where
  counter : Nat

def mkFresh : StateM Supply Nat := do
  let n ← (·.counter) <$> get
  modify fun s => { s with counter := s.counter + 1 }
  pure n

def mkFreshN (n : Nat) : StateM Supply (List Nat) := do
  let mut acc := #[]
  for _ in [:n] do
    acc := acc.push (← mkFresh)
  pure acc.toList

theorem mkFreshN_correct (n : Nat) : ((mkFreshN n).run' s).Nodup := by
  -- Focus on `(mkFreshN n).run' s`.
  generalize h : (mkFreshN n).run' s = x
  apply StateM.of_wp_run'_eq h
  -- Show something about monadic program `mkFresh n`.
  -- The `mkFreshN` and `mkFresh` arguments to `mvcgen` add to an
  -- internal `simp` set and makes `mvcgen` unfold these definitions.
  mvcgen [mkFreshN, mkFresh]
  invariants
  -- Invariant: The counter is larger than any accumulated number,
  --            and all accumulated numbers are distinct.
  -- Note that the invariant may refer to the state through function
  -- argument `state : Supply`. Since the next number to accumulate is
  -- the counter, it is distinct to all accumulated numbers.
  · ⇓⟨xs, acc⟩ state =>
      ⌜(∀ x ∈ acc, x < state.counter) ∧ acc.toList.Nodup⌝
  with grind
