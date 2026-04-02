

import LeanGrow.Src.Data.SetTrie.Theory.Model


open Finset



#check biUnion_biUnion
#check biUnion_insert

theorem Finset.biUnion_union  {β : Type _} {γ : Type _}
  [DecidableEq β] [DecidableEq γ]
  (x y : Finset β) (g : β → Finset γ) :
  (x ∪ y).biUnion g = x.biUnion g ∪ y.biUnion g := by
    induction x using Finset.induction with
    | empty => simp only [empty_union, biUnion_empty]
    | insert a b c ih =>
      rw [biUnion_insert, insert_union, biUnion_insert, union_assoc]
      congr


namespace StudyST

variable {α : Type} [DecidableEq α]

#check SetTrie.fold.induct

#check Finset.biUnion



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
  {head : SetTrie Unit (Finset α)} {tail : List (SetTrie Unit (Finset α))} {s : Finset α} :
  List.foldl (fun s t => t.fold s fun x y => x ∪ y) s (head :: tail) =
  head.fold (List.foldl (fun s t => t.fold s fun x y => x ∪ y) s tail) fun x y => x ∪ y := by
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


theorem sets_root_cons
  {head : SetTrie Unit (Finset α)} {tail : List (SetTrie Unit (Finset α))} :
  sets (SetTrie.root (head :: tail)) = (sets head) ∪ (sets (SetTrie.root tail)) := by
    -- unfold sets mapMerge SetTrie.mapMerge
    rw [sets, mapMerge, SetTrie.mapMerge]
    rw [List.map_cons]
    rw [List.foldl_assoc_comm_cons]
    congr
    rw [sets, mapMerge, SetTrie.mapMerge]


#check List.foldl_assoc_comm_cons


theorem fold_union_init
  {head : SetTrie Unit (Finset α)} {s : Finset α} :
  head.fold s (fun x y => x ∪ y) = s ∪ head.fold ∅ (fun x y => x ∪ y) := by
  revert s
  induction head, () using SetTrie.fold.induct with
  | case1 _ kids ih_kids =>
    induction kids with
    | nil =>
      intro _
      unfold SetTrie.fold
      dsimp
      rw [union_empty]
    | cons z zs ih =>
      intro s
      specialize @ih (fun u t mem s => @ih_kids u t (List.mem_cons_of_mem _ mem) s) s
      specialize @ih_kids () z (List.mem_cons_self) --((List.foldl (fun s t => t.fold s fun x y => x ∪ y) s zs))
      unfold SetTrie.fold
      rw [fold_cons, fold_cons, ih_kids, ih_kids]



#exit

theorem biUnion_sets_univ (st : StudyST α) : st.sets.biUnion id = st.univ := by
  induction st, () using SetTrie.fold.induct with
  | case1 _ kids ih_kids =>
    induction kids with
    | nil =>
      unfold sets univ fold SetTrie.fold mapMerge SetTrie.mapMerge
      rfl
    | cons head tail ih =>
      unfold univ fold SetTrie.fold -- sets mapMerge SetTrie.mapMerge
      rw [fold_cons]
      rw [sets_root_cons]
      rw [biUnion_union]
      specialize ih (fun u t mem => ih_kids u t (List.mem_cons_of_mem _ mem))
      specialize ih_kids () head (List.mem_cons_self)

  | case2 _ key kids ih_kids =>
    sorry
  | case3 _ =>
    unfold sets univ fold SetTrie.fold
    rfl
