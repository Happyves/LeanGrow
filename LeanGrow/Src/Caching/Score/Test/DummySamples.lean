


#check List.append_eq

open List

theorem test_1 (as : List α) (b : α) (bs : List α) : as ++ b :: bs = as ++ [b] ++ bs := by
  simp

theorem test_2 {as : List α} {a : α} : as.concat a = as ++ [a] := by
  induction as <;> simp [concat, *]

theorem test_3 {as bs : List α} : reverseAux as bs = reverseAux as [] ++ bs := by
  induction as generalizing bs with
  | nil => simp [reverseAux]
  | cons a as ih =>
    simp [reverseAux]

theorem test_4 {a : α} {as : List α} : reverse (a :: as) = reverse as ++ [a] := by
  unfold reverse
  rw [← List.reverseAux_eq_append]
  dsimp

variable {α : Type _} [BEq α]

theorem test_5 [LawfulBEq α] {l : List α} (h : a ∉ l) : l.replace a b = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [replace_cons]
    split <;> simp_all

theorem test_6 {l : List α} : (l.replace a b).length = l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [replace_cons]
    split <;> simp_all

theorem test_17 [LawfulBEq α] {l : List α} {i : Nat} :
    (l.replace a b)[i]? = if l[i]? == some a then if a ∈ l.take i then some a else some b else l[i]? := by
  induction l generalizing i with
  | nil => cases i <;> simp
  | cons x xs ih =>
    cases i <;>
    · simp only [replace_cons]
      split <;> split <;> simp_all

theorem test_8 [LawfulBEq α] {l : List α} {i : Nat} (h : l[i]? ≠ some a) :
    (l.replace a b)[i]? = l[i]? := by
  simp_all [List.getElem?_replace]

theorem test_9 [LawfulBEq α] {l : List α} {i : Nat} (h : i < l.length) :
    (l.replace a b)[i]'(by simpa) = if l[i] == a then if a ∈ l.take i then a else b else l[i] := by
  apply Option.some.inj
  rw [← getElem?_eq_getElem, getElem?_replace]
  split <;> split <;> simp_all

theorem test_10 [LawfulBEq α] {l : List α} {i : Nat} {h : i < l.length} (h' : l[i] ≠ a) :
    (l.replace a b)[i]'(by simpa) = l[i]'(h) := by
  rw [getElem_replace h]
  simp [h']

theorem test_11 {l : List α} {a b : α} :
    (l.replace a b).head? = match l.head? with
      | none => none
      | some x => some (if a == x then b else x) := by
  cases l with
  | nil => rfl
  | cons x xs =>
    simp [replace_cons]
    split <;> simp_all

theorem test_12 {l : List α} {a b : α} (w) :
    (l.replace a b).head w =
      if a == l.head (by rintro rfl; simp_all) then
        b
      else
        l.head  (by rintro rfl; simp_all) := by
  apply Option.some.inj
  rw [← head?_eq_head, head?_replace, head?_eq_head]

theorem test_13 [LawfulBEq α] {l₁ l₂ : List α} :
    (l₁ ++ l₂).replace a b = if a ∈ l₁ then l₁.replace a b ++ l₂ else l₁ ++ l₂.replace a b := by
  induction l₁ with
  | nil => simp
  | cons x xs ih =>
    simp only [cons_append, replace_cons]
    split <;> split <;> simp_all
