
-- # Insights from rewriting in LeanGrow

-- Rewriting under binders

example : (fun x y : Nat => x + y) = Nat.add :=
  have inside (x y : Nat) : x + y = y + x :=
    Nat.add_comm x y
  have first_binder (x : Nat) : (fun y => x + y) = (fun y => y + x) :=
    funext (fun y => inside x y)
  have second_binder : (fun x y => x + y) = (fun x y => y + x) :=
    funext (fun x => first_binder x)
  by
  refine @Eq.ndrec _ _ (fun p => p = Nat.add) ?newgoal _ second_binder.symm
  dsimp
  sorry


-- Pitfall : rewriting with conditions

#check Nat.add_div_left

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

example (n m : Nat) (x : Fin (n+m + 1)) : x.isNonZero (n+m) → 42 = 42 :=
  have reverted : ∀ (x : Fin (n+m + 1)), x.isNonZero (n+m) → 42 = 42 := by
    refine @Eq.ndrec _ _
      (fun p => ∀ (x : Fin (p + 1)), x.isNonZero p → 42 = 42)
      ?newgoal
      _ (Nat.add_comm m n)
    dsimp
    intro x
    sorry
  reverted x

/-
Remarks:

- LeanGrow only reverts fvars, but we can revert anything, including constants

- Very useful: reverting proofs !

- If let-bound fvars or defs for constants get reverted, we loose their value,
  which can prohibit cartain reductions: possible solution is to ζ or δ

-/
