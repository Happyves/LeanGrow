

#check 1


def List.sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + xs.sum

theorem PremOne (L : List Nat) (y : Nat) (h : ∀ x, x ∈ L → y ∣ x) : y ∣ L.sum := sorry

#check Nat.dvd_trans


set_option pp.all true in
#check PremOne
