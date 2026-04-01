

import LeanGrow.Src.Data.SetTrie.Theory.Model
import Mathlib.Data.Finset.Union


open Finset

namespace StudyST

variable {α : Type} [DecidableEq α]

#check SetTrie.fold.induct

#check Finset.biUnion

theorem biUnion_sets_univ (st : StudyST α) : st.sets.biUnion id = st.univ := by
  induction st, () using SetTrie.fold.induct with
  | case1 _ kids ih_kids =>
    unfold sets univ fold SetTrie.fold
    induction kids with
    | nil =>
      rfl
    | cons head tail ih =>
      sorry
  | case2 _ key kids ih_kids =>
    sorry
  | case3 _ =>
    unfold sets univ fold SetTrie.fold
    rfl


#check List.foldl_assoc_comm_cons


theorem fold_union_assoc (s k : Finset α) (a : SetTrie Unit (Finset α)) :
  a.fold s (fun x y => x ∪ y) ∪ k = a.fold (s ∪ k) (fun x y => x ∪ y) := by
    revert s k
    induction a, () using SetTrie.fold.induct with
    | case1 _ kids ih_kids =>
      unfold SetTrie.fold
      induction kids with
      | nil => intro _  _; rfl
      | cons z zs ih =>
        intro s k
        specialize ih (fun u t mem s => ih_kids u t (List.mem_cons_of_mem _ mem) s)
        dsimp
        specialize ih_kids () z (List.mem_cons_self) s
        rw [ih, ih_kids]
    | case2 _ key kids ih_kids =>
      unfold SetTrie.fold
      intro s k
      rw [union_assoc]
      nth_rewrite 2 [union_comm]
      rw [← union_assoc]
      congr 1 -- same as ↑
      revert s k
      induction kids with
      | nil => intro _  _; rfl
      | cons z zs ih =>
        intro s k
        specialize ih (fun u t mem s => ih_kids u t (List.mem_cons_of_mem _ mem) s)
        dsimp
        specialize ih_kids () z (List.mem_cons_self) s
        rw [ih, ih_kids]
    | case3 _ _ =>
      unfold SetTrie.fold
      intro _ _
      rfl





theorem fold_comm (s : Finset α) (a b : SetTrie Unit (Finset α)) :
  a.fold (b.fold s (fun x y => x ∪ y)) (fun x y => x ∪ y) =
    b.fold (a.fold s fun x y => x ∪ y) fun x y => x ∪ y := by
      revert b s
      induction a, () using SetTrie.fold.induct with
      | case1 _ kids ih_kids =>
        intro s b
        rw [SetTrie.fold]
        revert s
        induction kids with
        | nil =>
          intro _
          rw [SetTrie.fold]
          rfl
        | cons z zs ih =>
          intro s
          specialize ih (fun u t mem s b => ih_kids u t (List.mem_cons_of_mem _ mem) s b) (z.fold s fun x y => x ∪ y)
          dsimp
          specialize ih_kids () z (List.mem_cons_self) s b
          rw [ih_kids, ih]
          rw [SetTrie.fold, SetTrie.fold]
          rfl
      | case2 _ key kids ih_kids =>
        intro s b
        rw [SetTrie.fold]
        revert s
        induction kids with
        | nil =>
          intro s
          rw [SetTrie.fold]
          dsimp
          apply fold_union_assoc
        | cons z zs ih =>
          intro s
          specialize ih (fun u t mem s b => ih_kids u t (List.mem_cons_of_mem _ mem) s b) (z.fold s fun x y => x ∪ y)
          dsimp
          specialize ih_kids () z (List.mem_cons_self) s b
          rw [ih_kids, ih]
          rw [SetTrie.fold, SetTrie.fold]
          rfl
      | case3 _ _ =>
        intro _ _
        rw [SetTrie.fold, SetTrie.fold]


theorem fold_cons
  {head : SetTrie Unit (Finset α)} {tail : List (SetTrie Unit (Finset α))} :
  List.foldl (fun s t => t.fold s fun x y => x ∪ y) (∅ : Finset α) (head :: tail) =
  head.fold (List.foldl (fun s t => t.fold s fun x y => x ∪ y) ∅ tail) fun x y => x ∪ y := by
  generalize (∅ : Finset α) = s
  revert s
  induction tail generalizing head with
  | nil => intro _ ; rfl
  | cons z zs ih =>
    intro s
    rw [List.foldl_cons, List.foldl_cons]
    rw [fold_comm]
    rw [← List.foldl_cons]
    rw [ih]
    congr 1
