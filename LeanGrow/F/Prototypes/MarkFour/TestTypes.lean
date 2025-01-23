

#check 1


inductive myNat where
| z : myNat | s : myNat → myNat


def myAdd (l : myNat) : myNat → myNat
  | .z => l
  | .s r => .s (myAdd l r)

theorem myAdd_zero (r : myNat) : myAdd .z r = r := by
  apply @myNat.rec (fun x => myAdd .z x = x)
  · rfl
  · intro a ah
    unfold myAdd
    rw [ah]
