

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
    sorry
  | case2 _ key kids ih_kids =>
    sorry
  | case3 _ =>
    unfold sets univ fold SetTrie.fold
    rfl
