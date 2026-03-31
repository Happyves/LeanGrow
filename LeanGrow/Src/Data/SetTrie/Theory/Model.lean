

import LeanGrow.Src.Data.SetTrie.Operations
import Mathlib.Data.Finset.Card

open Finset

def StudyST (α : Type) := SetTrie Unit (Finset α)


variable {α : Type} [DecidableEq α]

def SetTrie.fold {γ : Type _} (c : SetTrie α β) (init : γ) (merge : γ → β → γ) : γ :=
  match c with
  | .root c => c.foldl (fun s t => (SetTrie.fold t s merge)) init
  | .node q c => merge (c.foldl (fun s t => (SetTrie.fold t s merge)) init) q
  | .leaf _ => init


namespace StudyST

abbrev fold {γ : Type _} (c : StudyST α) (init : γ) (merge : γ → (Finset α) → γ) : γ :=
  SetTrie.fold c init merge

def univ (st : StudyST α) : Finset α :=
  st.fold ∅ (fun x y => x ∪ y)

def size (st : StudyST α) : Nat :=
  st.fold 0 (fun x y => x + y.card)

def allNodes (st : StudyST α) (P : (Finset α) → Prop) : Prop :=
  st.fold True (fun x y => x ∧ P y)

def someNode (st : StudyST α) (P : (Finset α) → Prop) : Prop :=
  st.fold True (fun x y => x ∧ P y)

def hasElem (st : StudyST α) (a : α) : Prop :=
  st.someNode (fun x => a ∈ x)

def hasNode (st : StudyST α) (n : Finset α) : Prop :=
  st.someNode (fun x => n = x)

def sets (st : StudyST α) : Finset (Finset α) :=
  st.fold ∅ (fun x y => x.image (fun z => z ∪ y))
