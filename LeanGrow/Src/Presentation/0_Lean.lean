

-- # Refresher on Lean

-- Dependent types

#check Fin.mk 0 Nat.zero_lt_one
#check Fin.mk 0 Nat.zero_lt_two


-- Propositions as types, proofs as terms

theorem TheFundamentalTheoremOfSlideZero : 1 ≤ 2 :=
  Nat.succ_le_succ (Nat.zero_le 1)

#check Nat.zero_le
#check Nat.zero_le 1
#check Nat.succ_le_succ
#check Nat.succ_le_succ (Nat.zero_le 1)
#check TheFundamentalTheoremOfSlideZero


-- Induction via recursors

#check Nat.rec

example (a n : Nat) (h : 0 < a) : 0 < a^n := by
  refine Nat.rec ?base ?step n
  · apply Nat.zero_lt_succ
  · intro n ih
    apply Nat.mul_pos ih h
    -- ι-reduction happend

#check Nat.mul_pos
#check Nat.pow.eq_2


-- Rewriting as induction on equality

#check Eq.rec
#check Eq.ndrec

example (n m : Nat) (eq : n = m) (h : n + 5 = 42)  : m + 5 = 42 :=
  @Eq.ndrec _ n (fun p => p + 5 = 42) h m eq


variable (n m : Nat) (h : n + 5 = 42) (eq : n = m)
#check @Eq.ndrec _ n
#check @Eq.ndrec _ n (fun x => x + 5 = 42)
#check @Eq.ndrec _ n (fun x => x + 5 = 42) h
#check @Eq.ndrec _ n (fun x => x + 5 = 42) h m
#check @Eq.ndrec _ n (fun x => x + 5 = 42) h m eq
