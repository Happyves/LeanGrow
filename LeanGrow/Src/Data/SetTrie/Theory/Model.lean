

import LeanGrow.Src.Data.SetTrie.Operations
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort -- for repr instance
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Insert

open Finset

def StudyST (α : Type) := SetTrie Unit (Finset α)


variable {α : Type} [DecidableEq α]

def SetTrie.fold {γ : Type _} (c : SetTrie α β) (init : γ) (merge : γ → β → γ) : γ :=
  match c with
  | .root c => c.foldl (fun s t => (SetTrie.fold t s merge)) init
  | .node q c => merge (c.foldl (fun s t => (SetTrie.fold t s merge)) init) q
  | .leaf _ => init

#check 1

def SetTrie.mapMerge {γ : Type _} (c : SetTrie α β)
  (mergeR : List γ → γ) (mergeN : β → List γ → γ) (base : γ) : γ :=
  match c with
  | .root c => mergeR <| c.map (SetTrie.mapMerge · mergeR mergeN base)
  | .node q c => mergeN q <| c.map (SetTrie.mapMerge · mergeR mergeN base)
  | .leaf _ => base

def SetTrie.mapMergeDep {γ : Sort _} (c : SetTrie α β)
  (mergeR : List (SetTrie α β) → List γ → γ) (mergeN : β → List (SetTrie α β)→ List γ → γ) (base : γ) : γ :=
  match c with
  | .root c => mergeR c <| c.map (SetTrie.mapMergeDep · mergeR mergeN base)
  | .node q c => mergeN q c <| c.map (SetTrie.mapMergeDep · mergeR mergeN base)
  | .leaf _ => base


namespace StudyST

abbrev fold {γ : Type _} (c : StudyST α) (init : γ) (merge : γ → (Finset α) → γ) : γ :=
  SetTrie.fold c init merge

abbrev mapMerge {γ : Type _} (c : StudyST α) (mergeR : List γ → γ) (mergeN : (Finset α) → List γ → γ) (base : γ) : γ :=
  SetTrie.mapMerge c mergeR mergeN base

abbrev mapMergeDep {γ : Sort _} (c : StudyST α) (mergeR : List (StudyST α) → List γ → γ) (mergeN : (Finset α) → List (StudyST α)→ List γ → γ) (base : γ) : γ :=
  SetTrie.mapMergeDep c mergeR mergeN base


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
  st.mapMerge
    (fun c => c.foldl (fun x y => x ∪ y) (∅ : Finset (Finset α)))
    (fun q c => (c.foldl (fun x y => x ∪ y) ∅).image (fun z => q ∪ z))
    {∅}

def isRootP : StudyST α → Prop
  | .root _ => True
  | _ => False


/-- Nodes must have children, and there are no empty keys-/
def wf (st : StudyST α) : Prop :=
  st.mapMergeDep
    (fun _ r => r.foldl (· ∧ ·) True)
    (fun q c r => q ≠ ∅ ∧ c ≠ [] ∧ c.Forall (fun x => ¬ (isRootP x)) ∧ r.foldl (· ∧ ·) True)
    True


#exit


#check 1


def test : StudyST Nat :=
  .root
    [.node {1,2}
        [.node {3} [.leaf ()],
         .node {4} [.leaf ()]],
     .node {5} [.leaf ()]
    ]


#eval test.sets
