

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


lemma Finset.biUnion_union'  {α : Type u_1} {β : Type u_2} {s : Finset α} {t₁ t₂ : α → Finset β} [DecidableEq β]
  : s.biUnion (fun x ↦ t₁ x ∪ t₂ x) = s.biUnion t₁ ∪ s.biUnion t₂ := by grind
  -- added in recent mathlib under name Finset.biUnion_union


lemma Finset.biUnion_const {α : Type u_1} {β : Type u_2} [DecidableEq α] [DecidableEq β]
  {s : Finset α} {c : Finset β} (h : s ≠ ∅)
  : s.biUnion (fun _ ↦ c) = c := by
  induction s using Finset.induction with
  | empty => contradiction
  | insert x xs ih1 ih2 =>
    rw [biUnion_insert]
    by_cases q : xs ≠ ∅
    · rw [ih2 q, union_self]
    · rw [not_not] at q
      rw [q, biUnion_empty, union_empty]


--#exit

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
      specialize @ih (fun u t mem s => @ih_kids u t (List.mem_cons_of_mem _ mem) s)
      specialize @ih_kids () z (List.mem_cons_self)
      unfold SetTrie.fold
      rw [fold_cons, fold_cons, ih_kids]
      unfold SetTrie.fold at ih
      rw [ih]
      nth_rewrite 2 [ih_kids]
      rw [union_assoc]
  | case2 _ key kids ih_kids =>
    induction kids with
    | nil =>
      intro _
      unfold SetTrie.fold
      dsimp
      rw [← union_assoc, union_empty]
    | cons z zs ih =>
      intro s
      specialize @ih (fun u t mem s => @ih_kids u t (List.mem_cons_of_mem _ mem) s)
      specialize @ih_kids () z (List.mem_cons_self)
      unfold SetTrie.fold
      rw [fold_cons, fold_cons, ih_kids]
      unfold SetTrie.fold at ih
      rw [union_assoc]
      nth_rewrite 2 [union_comm]
      rw [← union_assoc]
      rw [ih]
      nth_rewrite 2 [ih_kids]
      rw [union_assoc]
      congr 1
      rw [union_assoc]
      nth_rewrite 2 [union_comm]
      rw [← union_assoc]
  | case3 _ _ =>
    intro _
    unfold SetTrie.fold
    rw [union_empty]





theorem univ_node_union_root
  {key : Finset α} {kids : List (SetTrie Unit (Finset α))} :
  univ (SetTrie.node key kids) = key ∪ univ (SetTrie.root kids) := by
  unfold univ fold SetTrie.fold
  rw [union_comm]

theorem sets_node_image_root
  {key : Finset α} {kids : List (SetTrie Unit (Finset α))} :
  sets (SetTrie.node key kids) = image (fun z => key ∪ z) (sets (SetTrie.root kids)) := by
    unfold sets mapMerge SetTrie.mapMerge
    dsimp


theorem wfRoot_of_cons_wfRoot
  (h : wfRoot (head :: tail)) : wfRoot tail := by
    cases tail with
    | nil =>
      constructor
      · simp only [List.Forall]
      · simp only [List.filter_nil, List.length_nil, Nat.zero_le]
    | cons x xs =>
      constructor
      · refine ((List.Forall.eq_3 _ _ _ ?_).mp h.kids_noroot).2
        simp only [reduceCtorEq, imp_self]
      · grind [wfRoot]

theorem wfNode_of_cons_wfNode
  (h : wfNode key (head :: tail)) (he : tail ≠ []) : wfNode key tail := by
    cases tail with
    | nil =>
      constructor
      · exact h.key_nonempty
      · exact he
      · simp only [List.Forall]
      · simp only [List.filter_nil, List.length_nil, Nat.zero_le]
    | cons x xs =>
      constructor
      · exact h.key_nonempty
      · exact he
      · refine ((List.Forall.eq_3 _ _ _ ?_).mp h.kids_noroot).2
        simp only [reduceCtorEq, imp_self]
      · grind [wfRoot, wfNode]



theorem root_wf_of_cons_wf
  (h : wf (SetTrie.root (head :: tail))) : wf (SetTrie.root tail) := by
    dsimp [wf, mapMergeDep] at h
    rw [SetTrie.mapMergeDep, List.map_cons, List.foldl_assoc_comm_cons] at h
    unfold wf mapMergeDep SetTrie.mapMergeDep
    constructor
    · apply wfRoot_of_cons_wfRoot h.1
    · apply h.2.2

theorem node_wf_of_cons_wf
  (h : wf (SetTrie.node key (head :: tail))) (he : tail ≠ []) : wf (SetTrie.node key tail) := by
    dsimp [wf, mapMergeDep] at h
    rw [SetTrie.mapMergeDep, List.map_cons, List.foldl_assoc_comm_cons] at h
    unfold wf mapMergeDep SetTrie.mapMergeDep
    constructor
    · apply wfNode_of_cons_wfNode h.1 he
    · apply h.2.2



theorem univ_root_cons :
  univ (SetTrie.root (head :: tail)) = (univ head : Finset α) ∪ (univ (SetTrie.root tail)) := by
    unfold univ fold
    rw [SetTrie.fold, fold_cons, fold_union_assoc, empty_union, SetTrie.fold]

theorem kids_root_wf_of_root_wf
  (h : wf (SetTrie.root tail)) : ∀ c ∈ tail, wf c := by
    induction tail with
    | nil => grind
    | cons x xs ih =>
      intro c ch
      rw [List.mem_cons] at ch
      cases ch with
      | inl ch =>
        rw [ch]
        clear ch
        unfold wf mapMergeDep SetTrie.mapMergeDep at h
        rw [List.map_cons, List.foldl_assoc_comm_cons] at h
        exact h.2.1
      | inr ch =>
        exact ih (root_wf_of_cons_wf h) c ch

theorem kids_node_wf_of_node_wf
  (h : wf (SetTrie.node key tail)) : ∀ c ∈ tail, wf c := by
    induction tail with
    | nil => grind
    | cons x xs ih =>
      intro c ch
      rw [List.mem_cons] at ch
      cases ch with
      | inl ch =>
        rw [ch]
        clear ch
        unfold wf mapMergeDep SetTrie.mapMergeDep at h
        rw [List.map_cons, List.foldl_assoc_comm_cons] at h
        exact h.2.1
      | inr ch =>
        refine ih (node_wf_of_cons_wf h ?_) c ch
        apply List.ne_nil_of_mem ch



theorem head_root_wf_of_cons_wf
  (h : wf (SetTrie.root (head :: tail))) : wf head := by
  apply kids_root_wf_of_root_wf h
  exact List.mem_cons_self


theorem tec_1
  (h1 : wf head) (h2 : ¬ isRootP head) : wf (SetTrie.root [head]) := by
    unfold wf mapMergeDep SetTrie.mapMergeDep
    rw [List.map_cons]
    simp only [List.map_nil, List.foldl_cons, true_and, List.foldl_nil]
    constructor
    · constructor
      · exact h2
      · apply le_trans (List.length_filter_le _ _)
        simp only [List.length_cons, List.length_nil, zero_add, le_refl]
    · exact h1


theorem univ_root_empty
  {kids : List (SetTrie Unit (Finset α))} (h : wf (SetTrie.root kids)) :
  univ (SetTrie.root kids) = ∅ ↔ (kids = [] ∨ kids = [.leaf ()]) := by
    induction kids with
    | nil =>
      unfold univ fold SetTrie.fold
      simp only [List.foldl_nil, List.ne_cons_self, or_false]
    | cons head tail ih =>
      specialize ih (root_wf_of_cons_wf h)
      constructor
      · intro q
        right
        rw [univ_root_cons, union_eq_empty] at q
        replace ih := ih.mp q.2
        cases ih with
        | inl ih =>
          rw [ih]
          congr
          cases head with
          | root _ =>
            rw [ih] at h
            unfold wf mapMergeDep SetTrie.mapMergeDep at h
            replace h := h.1.kids_noroot
            dsimp [isRootP] at h
            contradiction
          | node _ _ =>
            replace h := (head_root_wf_of_cons_wf h)
            unfold wf mapMergeDep SetTrie.mapMergeDep at h
            replace h := h.1.key_nonempty
            replace q := q.1
            unfold univ fold SetTrie.fold at q
            rw [union_eq_empty] at q
            exact False.elim (h q.2)
          | leaf _ =>
            rfl
        | inr ih =>
          cases head with
          | root _ => -- same as root case above
            rw [ih] at h
            unfold wf mapMergeDep SetTrie.mapMergeDep at h
            replace h := h.1.kids_noroot
            dsimp [isRootP] at h
            contradiction
          | node _ _ => -- same as node case above
            replace h := (head_root_wf_of_cons_wf h)
            unfold wf mapMergeDep SetTrie.mapMergeDep at h
            replace h := h.1.key_nonempty
            replace q := q.1
            unfold univ fold SetTrie.fold at q
            rw [union_eq_empty] at q
            exact False.elim (h q.2)
          | leaf _ =>
            rw [ih] at h
            unfold wf mapMergeDep SetTrie.mapMergeDep at h
            replace h := h.1.kids_one_leaf
            dsimp [isLeaf, List.filter] at h
            contradiction
      · intro Q
        simp only [reduceCtorEq, List.cons.injEq, false_or] at Q
        rw [Q.1, Q.2]
        unfold univ fold SetTrie.fold
        dsimp
        rw [SetTrie.fold]


theorem wf_root_of_wf_node
  (h : wf (SetTrie.node key kids)) : wf (SetTrie.root kids) := by
    unfold wf mapMergeDep SetTrie.mapMergeDep at *
    refine ⟨?_, h.2⟩
    constructor
    · exact h.1.kids_noroot
    · exact h.1.kids_one_leaf



theorem sets_node_cons :
  sets (SetTrie.node key (head :: tail)) = (image (fun z => key ∪ z) (sets head) : Finset (Finset α)) ∪ (sets (SetTrie.node key tail)) := by
    rw [sets, mapMerge, SetTrie.mapMerge]
    rw [List.map_cons]
    rw [List.foldl_assoc_comm_cons]
    rw [image_union]
    congr
    rw [sets, mapMerge, SetTrie.mapMerge]




theorem sets_root_empty
  {kids : List (SetTrie Unit (Finset α))} (h : wf (SetTrie.root kids)) :
  sets (SetTrie.root kids) = ∅ ↔ kids = [] := by
    induction kids with
    | nil =>
      unfold sets mapMerge SetTrie.mapMerge
      simp only [List.map_nil, List.foldl_nil]
    | cons x xs ih =>
      specialize ih (root_wf_of_cons_wf h)
      rw [sets_root_cons, union_eq_empty]
      simp only [reduceCtorEq, iff_false, not_and]
      intro a b
      rw [ih] at b
      rw [b] at h
      induction x, () using SetTrie.fold.induct with
      | case1 _ kids ih_kids =>
        unfold wf mapMergeDep SetTrie.mapMergeDep at h
        replace h := h.1.kids_noroot
        dsimp [isRootP] at h
        contradiction
      | case2 _ q kids ih_kids =>
        replace h := kids_root_wf_of_root_wf h _ (List.mem_cons_self)
        cases kids with
        | nil =>
          unfold wf mapMergeDep SetTrie.mapMergeDep at h
          replace h := h.1.kids_nonempty
          contradiction
        | cons z zs =>
          rw [sets_node_cons, union_eq_empty, image_eq_empty] at a
          apply ih_kids () z (List.mem_cons_self) ?_ a.1
          have h2 := kids_node_wf_of_node_wf h z List.mem_cons_self
          unfold wf mapMergeDep SetTrie.mapMergeDep
          dsimp
          refine ⟨?_,True.intro, h2⟩
          constructor
          · dsimp
            unfold wf mapMergeDep SetTrie.mapMergeDep at h
            have := h.1.kids_noroot
            cases zs with -- wier List.Forall requirement
            | nil =>
              rw [List.Forall.eq_2] at this
              exact this
            | cons _ _ =>
              rw [List.Forall.eq_3 _ _ _ (by simp)] at this
              exact this.1
          · grind
      | case3 _ =>
        rw [sets, mapMerge, SetTrie.mapMerge] at a
        apply notMem_empty (∅ : Finset α)
        rw [← a]
        exact mem_singleton.mpr rfl



theorem biUnion_sets_univ (st : StudyST α) (hwf : st.wf) : st.sets.biUnion id = st.univ := by
  have rq
    (kids : List (SetTrie Unit (Finset α))) (hwfk : wf (SetTrie.root kids))
    (ih_kids : ∀ (s : Unit), ∀ t ∈ kids, wf t → (sets t).biUnion id = univ t)
    : (sets (SetTrie.root kids)).biUnion id = univ (SetTrie.root kids) := by
      induction kids with
      | nil =>
        unfold sets univ fold SetTrie.fold mapMerge SetTrie.mapMerge
        rfl
      | cons head tail ih =>
        unfold univ fold SetTrie.fold -- sets mapMerge SetTrie.mapMerge
        rw [fold_cons]
        rw [sets_root_cons]
        rw [biUnion_union]
        specialize ih (root_wf_of_cons_wf hwfk) (fun u t mem => ih_kids u t (List.mem_cons_of_mem _ mem))
        specialize ih_kids () head (List.mem_cons_self)
        rw [fold_union_init]
        rw [union_comm]
        congr
        · unfold univ fold SetTrie.fold at ih
          apply ih
        · apply ih_kids (head_root_wf_of_cons_wf hwfk)
  induction st, () using SetTrie.fold.induct with
  | case1 _ kids ih_kids =>
    apply rq _ hwf ih_kids
  | case2 _ key kids ih_kids =>
    by_cases k : sets (SetTrie.root kids) = ∅
    · rw [sets_root_empty] at k
      rw [k] at hwf
      · unfold wf mapMergeDep SetTrie.mapMergeDep at hwf
        exfalso
        apply hwf.1.kids_nonempty
        rfl
      · apply wf_root_of_wf_node hwf

    · rw [univ_node_union_root, sets_node_image_root]
      rw [image_biUnion]
      dsimp
      rw [Finset.biUnion_union']
      rw [← rq kids (wf_root_of_wf_node hwf) ih_kids]
      congr
      rw [biUnion_const]
      exact k
  | case3 _ =>
    unfold sets univ fold SetTrie.fold mapMerge SetTrie.mapMerge
    rfl
