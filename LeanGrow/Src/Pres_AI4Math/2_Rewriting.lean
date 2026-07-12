
import Mathlib.Tactic

set_option linter.all false

-- # Insights from rewriting in LeanGrow

-- Rewriting under binders

example : (fun x y : Nat => y + x) = Nat.add := by
  rw [Nat.add_comm]
  rfl

example : (fun x y : Nat => y + x) = Nat.add := by
  simp_rw [Nat.add_comm]
  rfl

example : (fun x y : Nat => y + x) = Nat.add :=
  have inside (x y : Nat) : y+ x = x + y :=
    Nat.add_comm y x
  have first_binder (x : Nat) : (fun y => y + x) = (fun y => x + y) :=
    funext (fun y => inside x y)
  have second_binder : (fun x y => y + x) = (fun x y => x + y) :=
    funext (fun x => first_binder x)
  by
  refine @Eq.ndrec _ _ (fun p => p = Nat.add) ?newgoal _ second_binder.symm
  dsimp
  rfl

-- Pitfall : rewriting with conditions

#check Nat.add_div_left

example (a : Nat) : (fun (b : Nat) (h : 1 < b+1) => (b + a) / b) = (fun _ _ => 42) := by
  rw [Nat.add_div_left]
  sorry

example (a : Nat) : (fun (b : Nat) (h : 1 < b+1) => (b + a) / b) = (fun _ _ => 42) := by
  simp_rw [Nat.add_div_left] -- even though its registered @[simp]
  sorry

example (a : Nat) : (fun (b : Nat) (h : 1 < b+1) => (b + a) / b) = (fun _ _ => 42) :=
  have inside (b : Nat) (h : 1 < b+1) (ng : 1 < b+1 → 0 < b) :
    (b + a) / b = a / b + 1 :=
      Nat.add_div_left a (ng h)
  have first_binder (b : Nat) (ng : 1 < b+1 → 0 < b) :
    (fun (h : 1 < b+1) => (b + a) / b) = (fun _ => a / b + 1) :=
      funext (fun h => inside b h ng)
  have second_binder (ng : ∀ b, 1 < b+1 → 0 < b) :
    (fun b (h : 1 < b+1) => (b + a) / b) = (fun b _ => a / b + 1) :=
      funext (fun b => first_binder b (ng b))
  by
  refine @Eq.ndrec _ _ (fun p => p = (fun (b : Nat) (h : 1 < b+1) => 42))
    ?newgoal_main _ (second_binder ?newgoal_cond).symm
  · dsimp
    sorry
  · sorry


-- Rewriting with dependencies

def Fin.isNonZero (n : Nat) (x : Fin (n+1)) := x ≠ 0

example (n m : Nat) (x : Fin (n+m + 1)) : x.isNonZero (n+m) → ∃ y : Fin (m+n + 1), y.isNonZero (m+n) := by
  rw [Nat.add_comm]

example (n m : Nat) (x : Fin (n+m + 1)) : x.isNonZero (n+m) → ∃ y : Fin (m+n + 1), y.isNonZero (m+n) := by
  simp_rw [Nat.add_comm]

example (n m : Nat) (x : Fin (n+m + 1)) : x.isNonZero (n+m) → ∃ y : Fin (m+n + 1), y.isNonZero (m+n) :=
  have reverted : ∀ (x : Fin (n+m + 1)), x.isNonZero (n+m) → ∃ y : Fin (m+n + 1), y.isNonZero (m+n) := by
    refine @Eq.ndrec _ _
      (fun p => ∀ (x : Fin (p + 1)), x.isNonZero p → ∃ y : Fin (m+n + 1), y.isNonZero (m+n))
      ?newgoal
      _ (Nat.add_comm m n)
    dsimp
    intro x
    -- rewrite occurred
    intro H
    use x
  reverted x
