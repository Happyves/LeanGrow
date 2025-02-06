
import LeanGrow.F.Prototypes.MarkFour.Frontend
import LeanGrow.F.Prototypes.MarkFour.TestTypes

#check 1


example (L : List Nat) (a b : Nat) (h_dL : ∀ x, x ∈ L → b ∣ x) (h_dB : a ∣ b) :
  a ∣ L.sum := by
    apply PremOne
    intro x xl
    exact Nat.dvd_trans h_dB (h_dL x xl)

--#exit

#check 1

example (L : List Nat) (a b : Nat) (h_dL : ∀ x, x ∈ L → b ∣ x) (h_dB : a ∣ b) :
  a ∣ L.sum := by
    grow
    sorry

#check 1



example (L : List Nat) (a b : Nat) (h_dL : ∀ x, x ∈ L → b ∣ x) (h_dB : a ∣ b) :
  a ∣ L.sum := by
    growin
    sorry


#check 1


example (L : List Nat) (a b : Nat) (h_dL : ∀ x, x ∈ L → b ∣ x) (h_dB : a ∣ b) :
  a ∣ L.sum := by
    apply Nat.dvd_trans h_dB
    apply PremOne
    --exact h_dL
    -- ↑ grow ; ↓ growin
    intro x xl
    apply h_dL x xl


/-

TODO:
at back, allow for gnodes via Id and fix assembly


Old:
Take-aways :

- separate FixCtx into enivronement info, gnode info and lnode info.
  Forward steps shouldn't depend on lnodes, so that we can make versions of inferType
  and whnf that don't require this info ; then we can make forward steps independent
  of backward ones (the revrese ins't possible because of unification)

- unclear how to doe unification and backsteps in a meaningful way


-/
